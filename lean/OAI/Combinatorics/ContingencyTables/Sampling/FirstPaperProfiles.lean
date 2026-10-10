import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalLargeProfiles
import OAI.Combinatorics.ContingencyTables.Transport.CompletionCounts

namespace OAI

/-! # The first paper's supported assignments are its physical large choices -/

namespace ContingencyTables.FirstPaperProfiles

open scoped BigOperators Classical
open LargePairEnumeration PhysicalLargeProfiles CompletionCounts

variable {I J : Type*}

noncomputable def smallView (small : I → J → Bool)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ)
    (v : Bool) (i : I) (j : J) : ℕ :=
  if hs : small i j=true then z (⟨(i,j),hs⟩,v) else 0

/-- A choice for each large cell extends uniquely by zero on small cells,
exactly as used by the manuscript's supported residual completion sum. -/
noncomputable def supportedAssignmentEquiv (small : I → J → Bool) (B : I → J → ℕ) :
    PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) ≃
      Assignment small B where
  toFun a := ⟨fun i j => if hs : small i j=true then 0
      else a ⟨(i,j),Bool.eq_false_iff.mpr hs⟩,
    by intro i j hs; simp only [hs,dite_eq_left,Fin.val_zero]⟩
  invFun a l := a.val l.val.1 l.val.2
  left_inv a := by
    funext l
    have hs : small l.val.1 l.val.2=false := l.property
    simp [hs]
  right_inv a := by
    apply Subtype.ext
    funext i j
    by_cases hs : small i j=true
    · apply Fin.ext
      simp [hs,a.property i j hs]
    · simp [hs]

lemma physicalProfile_supported (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ)
    (a : Assignment small B) :
    physicalProfile (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) z
      ((supportedAssignmentEquiv small B).symm a)=
      PaddedCompletions.profile small B (smallView small z false) (smallView small z true)
        (assignmentMatrix a) := by
  funext u
  rcases u with ⟨⟨i,j⟩,v⟩
  by_cases hs : small i j=true
  · cases v <;> simp [physicalProfile,hs,PaddedCompletions.profile,smallView]
  · cases v <;> simp [physicalProfile,hs,PaddedCompletions.profile,
      supportedAssignmentEquiv,assignmentMatrix] <;> rfl

variable [Fintype I] [Fintype J]

/-- The finite product used in the signature proof counts exactly the
supported assignments used in the residual completion equivalence. -/
theorem physicalHardSum_eq_supported (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) :
    (∑ a : PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2),
      NestedPenaltyApplication.hardWeight RowColumnPenalties.cellLine
        (RowColumnPenalties.smallCoordinate small)
        (RowColumnPenalties.fullOffset B
          (fun i => r i+PaddedCompletions.rowLargeCount small i*L)
          (fun j => c j+PaddedCompletions.columnLargeCount small j*L)) RowColumnPenalties.viewSlope
        (RowColumnPenalties.smallOffset small B r c) RowColumnPenalties.viewSlope
        (physicalProfile (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) z a))=
      ∑ a : Assignment small B,
        if fullPenalty small B (smallView small z false) (smallView small z true)
          (assignmentMatrix a) r c L=0 then (1:ℝ) else 0 := by
  apply Fintype.sum_equiv (supportedAssignmentEquiv small B)
  intro a
  have he := physicalProfile_supported small B z ((supportedAssignmentEquiv small B) a)
  rw [Equiv.symm_apply_apply] at he
  rw [he]
  rfl

end ContingencyTables.FirstPaperProfiles

end OAI
