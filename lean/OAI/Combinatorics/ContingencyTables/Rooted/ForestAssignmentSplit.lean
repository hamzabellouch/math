import OAI.Combinatorics.ContingencyTables.Rooted.ForestLiteralCount
import OAI.Combinatorics.ContingencyTables.Rooted.LargePairEnumeration

namespace OAI

/-!
# Splitting actual large-cell assignments into tree and free choices

The coordinate enumeration used for signatures and the graph completion
sum use exactly the same assignments. This finite equivalence records
that fact, including the larger signed tree intervals.
-/

namespace ContingencyTables.ForestAssignmentSplit

open scoped BigOperators Classical
open SimpleGraph LargePairEnumeration GraphCompletionCounts ForestCapacity ForestLiteralCount

variable {I J : Type*}

@[reducible] def FreeCell (small : I → J → Bool) (T : SimpleGraph (I⊕J)) :=
  {a : I×J // small a.1 a.2=false ∧ ¬T.Adj (.inl a.1) (.inr a.2)}

@[reducible] def FreeIndex (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (b : I → J → ℕ) := (a : FreeCell small T) → Fin (b a.val.1 a.val.2+1)

noncomputable def freeTable (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (b : I → J → ℕ) (a : FreeIndex small T b) (i : I) (j : J) : ℕ :=
  if h : small i j=false ∧ ¬T.Adj (.inl i) (.inr j) then (a ⟨(i,j),h⟩).val else 0

lemma freeTable_bound (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (b : I → J → ℕ) (a : FreeIndex small T b) (i : I) (j : J)
    (hs : small i j=false) (ht : ¬T.Adj (.inl i) (.inr j)) :
    freeTable small T b a i j≤b i j := by
  unfold freeTable
  rw [dite_eq_left ⟨hs,ht⟩]
  have h := (a ⟨(i,j),⟨hs,ht⟩⟩).isLt
  change (a ⟨(i,j),⟨hs,ht⟩⟩).val<b i j+1 at h
  omega

/-- The large-cell product is the tree-interval product times the
original free-cell product, each with multiplicity one. -/
noncomputable def assignmentSplit (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (d : ℕ) (b : I → J → ℕ) :
    ((a : LargeCell (fun a : I×J => small a.1 a.2)) →
      Fin (width T d b a.val.1 a.val.2+1)) ≃ TreeIndex T d b×FreeIndex small T b where
  toFun a :=
    ((fun t => Fin.cast (by simp only [width,t.property,ite_true])
      (a ⟨t.val,hTG t.property⟩)),
     fun f => Fin.cast (by simp only [width,f.property.2,ite_false])
      (a ⟨f.val,f.property.1⟩))
  invFun a l := if h : T.Adj (.inl l.val.1) (.inr l.val.2) then
      Fin.cast (by simp only [width,h,ite_true]) (a.1 ⟨l.val,h⟩)
    else Fin.cast (by simp only [width,h,ite_false]) (a.2 ⟨l.val,⟨l.property,h⟩⟩)
  left_inv a := by
    funext l
    by_cases ht : T.Adj (.inl l.val.1) (.inr l.val.2)
    · apply Fin.ext
      simp [ht]
    · apply Fin.ext
      simp [ht]
  right_inv a := by
    apply Prod.ext
    · funext t
      apply Fin.ext
      simp [t.property]
    · funext f
      apply Fin.ext
      simp [f.property.2]

/-- A tree/free split assignment gives precisely the cell counts in the
literal graph profile, before taking the complementary column view. -/
lemma split_cellCount (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (d : ℕ) (b : I → J → ℕ)
    (a : TreeIndex T d b×FreeIndex small T b)
    (l : LargeCell (fun a : I×J => small a.1 a.2)) :
    (((assignmentSplit small T hTG d b).symm a l).val)=
      cellCount T d b (freeTable small T b a.2) a.1 l.val.1 l.val.2 := by
  by_cases ht : T.Adj (.inl l.val.1) (.inr l.val.2)
  · simp [assignmentSplit,Equiv.symm,ht,cellCount]
  · simp [assignmentSplit,Equiv.symm,ht,cellCount,freeTable,l.property]

end ContingencyTables.ForestAssignmentSplit

end OAI
