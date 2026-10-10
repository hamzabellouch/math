import OAI.NumberTheory.Ostmann.Characters.TemplateParityActionsPermutation

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template.ParityActions
attribute [local instance] Classical.propDecidable

theorem anchor_entry_isUnit (k l : ℕ) (hl : l ≤ k) (big : Bool)
    (w : Word k l) (j : Fin l) (b : Bool) :
    IsUnit (graph k l (retiredAnchors k l hl big j b).val w.val) := by
  have hh := graph_anchor_code k l hl big w j
  cases b with
  | false => rw [hh.2]; exact (rowSign k l w.val).isUnit.mul (Units.isUnit _)
  | true => rw [hh.1]; exact (rowSign k l w.val).isUnit.mul (Units.isUnit _)

theorem same_parity_anchor_difference (k l : ℕ) (hl : l ≤ k)
    {w z : Word k l} (hne : w ≠ z)
    (hs : rowSign k l w.val = rowSign k l z.val) :
    ∃ j : Fin l, ∃ b : Bool,
      (graph k l (retiredAnchors k l hl false j b).val w.val -
        graph k l (retiredAnchors k l hl false j b).val z.val = 2 ∨
       graph k l (retiredAnchors k l hl false j b).val w.val -
        graph k l (retiredAnchors k l hl false j b).val z.val = -2) ∧
      graph k l w.val (retiredAnchors k l hl false j b).val -
        graph k l z.val (retiredAnchors k l hl false j b).val = 0 := by
  obtain ⟨j,b,hentry⟩ := exists_changed_anchor_entry k l hl false hne hs
  refine ⟨j,b,?_,?_⟩
  · rcases Int.isUnit_eq_one_or (anchor_entry_isUnit k l hl false w j b) with hw | hw <;>
    rcases Int.isUnit_eq_one_or (anchor_entry_isUnit k l hl false z j b) with hz | hz <;>
    simp_all
  · rw [graph_word_retiredAnchor k l hl false w j b,
      graph_word_retiredAnchor k l hl false z j b,hs,sub_self]

theorem distinct_reassignments_anchor (k n m : ℕ) (hn : n+1 ≤ k)
    {σ ρ : Reassignments k n m} (h : σ ≠ ρ) :
    ∃ z : BulkSlot k n m, ∃ j : Fin (n+1), ∃ b : Bool,
      (bulkPermutation k n m σ z).2 = (bulkPermutation k n m ρ z).2 ∧
      rowSign k (n+1) (bulkPermutation k n m σ z).1.val =
        rowSign k (n+1) (bulkPermutation k n m ρ z).1.val ∧
      (graph k (n+1) (retiredAnchors k (n+1) hn false j b).val
          (bulkPermutation k n m σ z).1.val -
        graph k (n+1) (retiredAnchors k (n+1) hn false j b).val
          (bulkPermutation k n m ρ z).1.val = 2 ∨
       graph k (n+1) (retiredAnchors k (n+1) hn false j b).val
          (bulkPermutation k n m σ z).1.val -
        graph k (n+1) (retiredAnchors k (n+1) hn false j b).val
          (bulkPermutation k n m ρ z).1.val = -2) ∧
      graph k (n+1) (bulkPermutation k n m σ z).1.val
          (retiredAnchors k (n+1) hn false j b).val -
        graph k (n+1) (bulkPermutation k n m ρ z).1.val
          (retiredAnchors k (n+1) hn false j b).val = 0 := by
  obtain ⟨z,hne,hpos,hs⟩ := exists_distinct_destinations k n m h
  obtain ⟨j,b,hforward,hreverse⟩ := same_parity_anchor_difference k (n+1) hn hne hs
  exact ⟨z,j,b,hpos,hs,hforward,hreverse⟩

end Ostmann.Characters.Template.ParityActions

end

end OAI
