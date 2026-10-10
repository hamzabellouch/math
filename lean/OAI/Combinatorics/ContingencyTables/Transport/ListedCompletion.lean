import OAI.Combinatorics.ContingencyTables.Transport.TableMarginTransport
import OAI.Combinatorics.ContingencyTables.Rooted.LargeMarginReference
import OAI.Combinatorics.ContingencyTables.Transport.CompletionFibreEquiv
import OAI.Combinatorics.ContingencyTables.Transport.ReferenceCompletionBounds

namespace OAI

/-! # Entry-preserving completion coordinates in computed list order -/

namespace ContingencyTables.SmallGraphProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions
open DensePrograms
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}
variable (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ) (B : Fin m → Fin n → ℕ)
variable (hr : 0 < (ProfilePrograms.largeIndices (U,List.ofFn r)).length)
variable (hc : 0 < (ProfilePrograms.largeIndices (U,List.ofFn c)).length)

def listedReferenceIndex (r : Fin m → ℕ) (U : ℕ)
    (hr : 0 < (ProfilePrograms.largeIndices (U,List.ofFn r)).length) :
    Option (Fin ((ProfilePrograms.largeIndices (U,List.ofFn r)).length-1)) ≃
      Option {i : LargeRows r U // i≠largeOptionEquiv r U hr none} :=
  (largeOptionEquiv r U hr).trans (Equiv.optionSubtypeNe (largeOptionEquiv r U hr none)).symm

lemma listedReference_row
    (z : PhysicalStates (firstPaperSmall r c U) B r c L) :
    (fun i => referenceRows r c U L B (largeOptionEquiv r U hr none) z
      (listedReferenceIndex r U hr i))=listedRows r c U L B hr z := by
  funext i
  simp only [referenceRows,listedReferenceIndex,Equiv.trans_apply,Equiv.apply_symm_apply,listedRows]

lemma listedReference_column
    (z : PhysicalStates (firstPaperSmall r c U) B r c L) :
    (fun j => referenceColumns r c U L B (largeOptionEquiv c U hc none) z
      (listedReferenceIndex c U hc j))=listedColumns r c U L B hc z := by
  funext j
  simp only [referenceColumns,listedReferenceIndex,Equiv.trans_apply,Equiv.apply_symm_apply,listedColumns]

def listedFibreEquiv (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k)≤B i j) :
    CompletionFibre (firstPaperSmall r c U) B r
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L) c
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L)
      (physicalProfile _ B r c L z) ≃ Table (listedRows r c U L B hr z) (listedColumns r c U L B hc z) := by
  let i₀ := largeOptionEquiv r U hr none
  let j₀ := largeOptionEquiv c U hc none
  have E := (referenceFibreEquiv r c U L B i₀ j₀ z hcap).trans
    (tableReindex (listedReferenceIndex r U hr) (listedReferenceIndex c U hc)
      (referenceRows r c U L B i₀ z) (referenceColumns r c U L B j₀ z))
  exact E.trans (tableMarginTransport _ _ _ _
    (listedReference_row r c U L B hr z) (listedReference_column r c U L B hc z))

lemma listedFibreEquiv_entry (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k)≤B i j)
    (A : CompletionFibre (firstPaperSmall r c U) B r
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L) c
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L)
      (physicalProfile _ B r c L z)) (i) (j) :
    (listedFibreEquiv r c U L B hr hc z hcap A).val i j=
      (referenceFibreEquiv r c U L B (largeOptionEquiv r U hr none)
        (largeOptionEquiv c U hc none) z hcap A).val
          (listedReferenceIndex r U hr i) (listedReferenceIndex c U hc j) := rfl

theorem listed_totals (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k)≤B i j) :
    (∑ i,listedRows r c U L B hr z i)=∑ j,listedColumns r c U L B hc z j := by
  have h := reference_totals r c U L B (largeOptionEquiv r U hr none)
    (largeOptionEquiv c U hc none) z hcap
  rw [←(listedReferenceIndex r U hr).sum_comp
      (referenceRows r c U L B (largeOptionEquiv r U hr none) z),
    ←(listedReferenceIndex c U hc).sum_comp
      (referenceColumns r c U L B (largeOptionEquiv c U hc none) z)] at h
  simpa only [listedReference_row,listedReference_column] using h

include hc in
theorem listed_row_padding (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (i : Option (Fin ((ProfilePrograms.largeIndices (U,List.ofFn r)).length-1))) :
    L≤listedRows r c U L B hr z i :=
  large_row_padding r c U L B z (largeOptionEquiv r U hr i) (largeOptionEquiv c U hc none)

include hr in
theorem listed_column_padding (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (j : Option (Fin ((ProfilePrograms.largeIndices (U,List.ofFn c)).length-1))) :
    L≤listedColumns r c U L B hc z j :=
  large_column_padding r c U L B z (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc j)

end
end ContingencyTables.SmallGraphProfiles

end OAI
