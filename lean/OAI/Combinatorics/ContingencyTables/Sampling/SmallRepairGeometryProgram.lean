import OAI.Combinatorics.ContingencyTables.Sampling.ProfileInverseRepairProgram
import OAI.Combinatorics.ContingencyTables.Sampling.SmallProfileCode

namespace OAI

/-! # Binary computation of repair crossing cells and capacities -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

abbrev RepairGeometry := List (ℕ×ℕ)×(ℕ×ℕ)

def sourceCell : Realizer (fun z : RepairGeometry => z.1.getD z.2.1 (0,0)) :=
  composition (pair first (composition second first)) (getDFast (0,0))

def targetCell : Realizer (fun z : RepairGeometry => z.1.getD z.2.2 (0,0)) :=
  composition (pair first (composition second second)) (getDFast (0,0))

lemma polynomial_sourceCell : PolynomialTime sourceCell :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_first)) (polynomial_getDFast (0,0))

lemma polynomial_targetCell : PolynomialTime targetCell :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_second)) (polynomial_getDFast (0,0))

def crossingIndex (z : RepairGeometry) : ℕ :=
  z.1.idxOf ((z.1.getD z.2.2 (0,0)).1,(z.1.getD z.2.1 (0,0)).2)

def crossingIndexRealizer : Realizer crossingIndex :=
  composition (pair (pair (composition targetCell first) (composition sourceCell second)) first)
    cellLookupRealizer

theorem polynomial_crossingIndex : PolynomialTime crossingIndexRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_targetCell polynomial_first)
    (polynomial_composition polynomial_sourceCell polynomial_second)) polynomial_first)
    polynomial_cellLookup

def capacityList (z : ℕ×List ℕ) : List ℕ := z.2.map (fun _ => z.1)

def capacityListRealizer : Realizer capacityList := mapWith first

theorem polynomial_capacityList : PolynomialTime capacityListRealizer :=
  polynomial_mapWith polynomial_first

lemma capacityList_ofFn {q : ℕ} (U : ℕ) (v : Fin q → ℕ) :
    capacityList (U,List.ofFn v)=List.ofFn (fun _ : Fin q => U) := by
  simp only [capacityList,List.map_ofFn,Function.comp_def]

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

lemma catalog_getD (i : Fin q) :
    (cellCatalog small e).getD i.val (0,0)=((e i).val.1.val,(e i).val.2.val) := by
  simp only [cellCatalog,List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,
    dite_true,Option.getD_some,Fin.eta]

/-- Large crossing cells use the out-of-range index in both the
forward and inverse arithmetic repairs. -/
theorem crossingIndex_eq (s t : Cells small) :
    crossingIndex (cellCatalog small e,((e.symm s).val,(e.symm t).val))=
      cellIndex small e (t.val.1,s.val.2) := by
  unfold crossingIndex
  rw [catalog_getD,catalog_getD]
  simp only [Equiv.apply_symm_apply]
  exact cellCatalog_index small e (t.val.1,s.val.2)

end
end ContingencyTables.SmallGraphProfiles

end OAI
