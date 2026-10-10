import OAI.Combinatorics.ContingencyTables.Rooted.LargeMarginProgram
import OAI.Combinatorics.ContingencyTables.Sampling.PaddedResidualSemantics
import OAI.Combinatorics.ContingencyTables.Transport.ReferenceCompletionBlock

namespace OAI

/-! # Exact indexing of the computed large residual margins -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms PaddedCompletions SmallContextCoordinates SmallContextFibres
open PhysicalCompletionFibres FirstPaperProfiles CompletionCounts
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ}

lemma largeIndices_ofFn_mem (r : Fin m → ℕ) (U : ℕ) (i : Fin m) :
    i.val∈largeIndices (U,List.ofFn r) ↔ U≤r i := by
  rw [mem_largeIndices]
  simp only [List.length_ofFn,i.isLt,true_and,List.getD_eq_getElem?_getD,
    List.getElem?_ofFn,dite_true,Option.getD_some,Fin.eta]

private def largeMemberEquiv (r : Fin m → ℕ) (U : ℕ) :
    {i // i∈largeIndices (U,List.ofFn r)} ≃ LargeRows r U where
  toFun x := by
    have hm := (mem_largeIndices U (List.ofFn r) x.val).mp x.property
    have hi : x.val < m := by simpa only [List.length_ofFn] using hm.1
    exact ⟨⟨x.val,hi⟩,(largeIndices_ofFn_mem r U ⟨x.val,hi⟩).mp x.property⟩
  invFun i := ⟨i.val.val,(largeIndices_ofFn_mem r U i.val).mpr i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Increasing list order gives a fixed, computed indexing of every
large row. The same construction is used for columns. -/
def largeIndexEquiv (r : Fin m → ℕ) (U : ℕ) :
    Fin (largeIndices (U,List.ofFn r)).length ≃ LargeRows r U :=
  (List.Nodup.getEquiv _ (largeIndices_nodup U (List.ofFn r))).trans (largeMemberEquiv r U)

lemma largeIndexEquiv_val (r : Fin m → ℕ) (U : ℕ)
    (i : Fin (largeIndices (U,List.ofFn r)).length) :
    (largeIndexEquiv r U i).val.val=(largeIndices (U,List.ofFn r))[i.val] := rfl

lemma largePaddedMargins_ofFn (row : Bool) (z : PaddingData) :
    largePaddedMargins row z=List.ofFn
      (fun i : Fin (largeIndices (z.1.2,marginList row z.1)).length =>
        paddedMarginAt row (z,(largeIndices (z.1.2,marginList row z.1))[i.val])) := by
  rw [largePaddedMargins_eq]
  exact (List.ofFn_getElem_eq_map _ _).symm

theorem largePaddedRows_code (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (e : Fin q ≃ Cells (firstPaperSmall r c U))
    (z : SmallProfile (firstPaperSmall r c U)) :
    largePaddedMargins true
      (((((cellCatalog (firstPaperSmall r c U) e,viewList (firstPaperSmall r c U) e z false),
        (List.ofFn r,List.ofFn c)),U),L))=
      List.ofFn (fun i : Fin (largeIndices (U,List.ofFn r)).length =>
        r (largeIndexEquiv r U i).val-
          smallRow (firstPaperSmall r c U) (smallView (firstPaperSmall r c U) z false)
            (largeIndexEquiv r U i).val+
          rowLargeCount (firstPaperSmall r c U) (largeIndexEquiv r U i).val*L) := by
  rw [largePaddedMargins_ofFn]
  apply congrArg List.ofFn
  funext i
  exact paddedRowAt_code r c U L e z (largeIndexEquiv r U i).val

theorem largePaddedColumns_code (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (e : Fin q ≃ Cells (firstPaperSmall r c U))
    (B : Fin m → Fin n → ℕ) (hB : ∀ a : Cells (firstPaperSmall r c U),B a.val.1 a.val.2=U)
    (z : SmallProfile (firstPaperSmall r c U)) :
    largePaddedMargins false
      (((((cellCatalog (firstPaperSmall r c U) e,
        complementValues (U,viewList (firstPaperSmall r c U) e z true)),
        (List.ofFn r,List.ofFn c)),U),L))=
      List.ofFn (fun j : Fin (largeIndices (U,List.ofFn c)).length =>
        c (largeIndexEquiv c U j).val-
          smallColumn (firstPaperSmall r c U) B (smallView (firstPaperSmall r c U) z true)
            (largeIndexEquiv c U j).val+
          columnLargeCount (firstPaperSmall r c U) (largeIndexEquiv c U j).val*L) := by
  rw [largePaddedMargins_ofFn]
  apply congrArg List.ofFn
  funext j
  exact paddedColumnAt_code r c U L e B hB z (largeIndexEquiv c U j).val

end
end ContingencyTables.SmallGraphProfiles

end OAI
