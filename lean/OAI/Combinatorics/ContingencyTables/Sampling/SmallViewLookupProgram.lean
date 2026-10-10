import OAI.Combinatorics.ContingencyTables.Sampling.SmallCellCatalogProgram

namespace OAI

/-! # Polynomial lookup of the sparse small-cell view -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

abbrev ViewLookupInput := (List (ℕ×ℕ)×List ℕ)×(ℕ×ℕ)

def lookupView (z : ViewLookupInput) : ℕ :=
  z.1.2.getD (z.1.1.idxOf z.2) 0

def lookupViewRealizer : Realizer lookupView :=
  composition (pair (composition first second)
    (composition (pair second (composition first first)) cellLookupRealizer)) (getDFast 0)

theorem polynomial_lookupView : PolynomialTime lookupViewRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition polynomial_first polynomial_first)) polynomial_cellLookup))
    (polynomial_getDFast 0)

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

/-- Missing large cells yield zero, exactly as required by `smallView`. -/
theorem lookupView_eq (z : SmallProfile small) (b : Bool) (i : Fin m) (j : Fin n) :
    lookupView ((cellCatalog small e,viewList small e z b),(i.val,j.val))=
      smallView small z b i j := by
  unfold lookupView
  rw [cellCatalog_index small e (i,j)]
  by_cases hs : small i j=true
  · simp only [cellIndex,dite_eq_left hs,viewList,List.getD_eq_getElem?_getD,
      List.getElem?_ofFn,(e.symm ⟨(i,j),hs⟩).isLt,dite_true,Option.getD_some,
      smallView]
    change z (e (e.symm ⟨(i,j),hs⟩),b)=z (⟨(i,j),hs⟩,b)
    rw [Equiv.apply_symm_apply]
  · simp only [cellIndex,dite_eq_right hs,viewList,List.getD_eq_getElem?_getD,
      List.getElem?_ofFn,lt_self_iff_false,dite_false,Option.getD_none,smallView]

end
end ContingencyTables.SmallGraphProfiles

end OAI
