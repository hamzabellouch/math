import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalOriginalResiduals
import OAI.Combinatorics.ContingencyTables.Transport.ReferenceCompletionBlock
import OAI.Combinatorics.ContingencyTables.Transport.TableMarginTransport

namespace OAI

/-!
# Entry-preserving completion equivalences

The finite dense draw is transported to the retained completion fibre by
an equivalence preserving every table entry.
-/

namespace ContingencyTables.PhysicalCompletionFibres

open scoped BigOperators Classical
open LargePairEnumeration PhysicalLargeProfiles RowColumnPenalties
open FirstPaperPhysicalMarginal FirstPaperProfiles PaddedCompletions CompletionCounts

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev ZeroPhysical (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : SmallProfile small) :=
  {a : PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2) //
    NestedPenaltyApplication.penalty cellLine (smallCoordinate small)
      (fullOffset B (fun i => r i+rowLargeCount small i*L)
        (fun j => c j+columnLargeCount small j*L)) viewSlope
      (smallOffset small B r c) viewSlope
      (PhysicalLargeProfiles.physicalProfile (fun a : I×J => small a.1 a.2)
        (fun a => B a.1 a.2) z a)=0}

noncomputable def zeroSupportedEquiv (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : SmallProfile small) :
    ZeroPhysical small B r c L z ≃
      ZeroAssignments small B (smallView small z false) (smallView small z true) r c L :=
  (supportedAssignmentEquiv small B).subtypeEquiv (fun a => by
    have h := physicalProfile_supported small B z ((supportedAssignmentEquiv small B) a)
    rw [Equiv.symm_apply_apply] at h
    change _=0 ↔ fullPenalty small B _ _ _ r c L=0
    rw [h]
    rfl)

noncomputable def fibreLargeEquiv (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : SmallProfile small)
    (hz : ∀ u,z u ≤ B u.1.val.1 u.1.val.2)
    (hres : OriginalResidualsNonnegative small B (smallView small z false) (smallView small z true) r c)
    (hcap : ∀ i j,small i j=false →
      (∑ k,(r k-smallRow small (smallView small z false) k+rowLargeCount small k*L)) ≤ B i j) :
    CompletionFibre small B r (fun i => r i+rowLargeCount small i*L)
      c (fun j => c j+columnLargeCount small j*L) z ≃
    LargeCompletion small
      (fun i => r i-smallRow small (smallView small z false) i+rowLargeCount small i*L)
      (fun j => c j-smallColumn small B (smallView small z true) j+columnLargeCount small j*L) :=
  ((zeroPhysicalEquiv small B r c L z hz).symm.trans
    (zeroSupportedEquiv small B r c L z)).trans
    (completionEquiv small B (smallView small z false) (smallView small z true) r c L
      (fun i j hs => by simpa only [smallView,hs,dite_eq_left] using hz (⟨(i,j),hs⟩,false))
      (fun i j hs => by simpa only [smallView,hs,dite_eq_left] using hz (⟨(i,j),hs⟩,true)) hres hcap)

lemma fibreLargeEquiv_apply (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : SmallProfile small)
    (hz : ∀ u,z u ≤ B u.1.val.1 u.1.val.2)
    (hres : OriginalResidualsNonnegative small B (smallView small z false) (smallView small z true) r c)
    (hcap : ∀ i j,small i j=false →
      (∑ k,(r k-smallRow small (smallView small z false) k+rowLargeCount small k*L)) ≤ B i j)
    (Z : CompletionFibre small B r (fun i => r i+rowLargeCount small i*L)
      c (fun j => c j+columnLargeCount small j*L) z) (i : I) (j : J) :
    (fibreLargeEquiv small B r c L z hz hres hcap Z).val.val i j=
      if small i j then 0 else Z.val.val.1 i j := by
  change (if hs : small i j=true then (0 : Fin (B i j+1))
    else fibreAssignment Z ⟨(i,j),Bool.eq_false_iff.mpr hs⟩).val=_
  by_cases hs : small i j=true
  · simp only [hs,dite_eq_left,ite_true,Fin.val_zero]
  · simp only [hs]
    rfl

end ContingencyTables.PhysicalCompletionFibres

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions
open SmallContextFibres

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Actual retained completion fibre to the fixed-reference dense block. -/
noncomputable def referenceFibreEquiv (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j) :
    CompletionFibre (firstPaperSmall r c U) B r
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L) c
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L)
      (physicalProfile _ B r c L z) ≃
    Table (referenceRows r c U L B i₀ z) (referenceColumns r c U L B j₀ z) := by
  refine ((fibreLargeEquiv (firstPaperSmall r c U) B r c L
    (physicalProfile _ B r c L z) (naturalProfile_bounded z.val.val)
    (physical_original_residuals _ B r c L z hcap) hcap).trans ?_).trans
    (tableReindex (Equiv.optionSubtypeNe i₀) (Equiv.optionSubtypeNe j₀)
      (fun i : LargeRows r U => residualRows (firstPaperSmall r c U) B r c L z i.val)
      (fun j : LargeColumns c U => residualColumns (firstPaperSmall r c U) B r c L z j.val))
  let E := rectangleCompletionEquiv (firstPaperSmall r c U)
    (fun i => U ≤ r i) (fun j => U ≤ c j) (firstPaperSmall_false_iff r c U)
    (residualRows _ B r c L z) (residualColumns _ B r c L z)
    (physical_residual_row_zero r c U L B z hcap)
    (physical_residual_column_zero r c U L B z hcap)
  exact E.trans (tableFintypeTransport _ _ _ _ _ _)

end ContingencyTables.SmallGraphProfiles

end OAI
