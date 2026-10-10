import OAI.Combinatorics.ContingencyTables.Sampling.SmallRepairGeometryProgram

namespace OAI

/-! # Forward and inverse repairs on the stored pair of integer lists -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

abbrev RepairData := (List (ℕ×ℕ)×(List ℕ×List ℕ))×ℕ
abbrev LabelledRepairData := RepairData×(ℕ×ℕ)

def repairDataCatalog : Realizer (fun z : LabelledRepairData => z.1.1.1) :=
  composition (composition first first) first

def repairDataRows : Realizer (fun z : LabelledRepairData => z.1.1.2.1) :=
  composition (composition (composition first first) second) first

lemma polynomial_repairDataCatalog : PolynomialTime repairDataCatalog :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first

lemma polynomial_repairDataRows : PolynomialTime repairDataRows :=
  polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first

def repairDataCaps : Realizer (fun z : LabelledRepairData =>
    capacityList (z.1.2,z.1.1.2.1)) :=
  composition (pair (composition first second) repairDataRows) capacityListRealizer

lemma polynomial_repairDataCaps : PolynomialTime repairDataCaps :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second) polynomial_repairDataRows)
    polynomial_capacityList

def repairDataCross : Realizer (fun z : LabelledRepairData =>
    crossingIndex (z.1.1.1,z.2)) :=
  composition (pair repairDataCatalog second) crossingIndexRealizer

lemma polynomial_repairDataCross : PolynomialTime repairDataCross :=
  polynomial_composition (polynomial_pair polynomial_repairDataCatalog polynomial_second)
    polynomial_crossingIndex

def forwardRepairCode (z : LabelledRepairData) : List ℕ×List ℕ :=
  repairedViews (z.1.1.2.1,(capacityList (z.1.2,z.1.1.2.1),
    (z.2.2,crossingIndex (z.1.1.1,z.2))))

def forwardRepairCodeRealizer : Realizer forwardRepairCode :=
  composition (pair repairDataRows (pair repairDataCaps
    (pair (composition second second) repairDataCross))) repairedViewsRealizer

theorem polynomial_forwardRepairCode : PolynomialTime forwardRepairCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_repairDataRows
    (polynomial_pair polynomial_repairDataCaps
      (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
        polynomial_repairDataCross))) polynomial_repairedViews

def inverseRepairCode (z : LabelledRepairData) : List ℕ×List ℕ :=
  backwardViews (z.1.1.2.1,(capacityList (z.1.2,z.1.1.2.1),
    (z.2.1,(z.2.2,crossingIndex (z.1.1.1,z.2)))))

def inverseRepairCodeRealizer : Realizer inverseRepairCode :=
  composition (pair repairDataRows (pair repairDataCaps
    (pair (composition second first) (pair (composition second second) repairDataCross))))
      backwardViewsRealizer

theorem polynomial_inverseRepairCode : PolynomialTime inverseRepairCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_repairDataRows
    (polynomial_pair polynomial_repairDataCaps
      (polynomial_pair (polynomial_composition polynomial_second polynomial_first)
        (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
          polynomial_repairDataCross)))) polynomial_backwardViews

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

theorem forwardRepairCode_eq (B : Fin m → Fin n → ℕ) (U : ℕ)
    (hU : ∀ a : Cells small,B a.val.1 a.val.2=U) (z : SmallProfile small)
    (s t : Cells small) :
    forwardRepairCode (((cellCatalog small e,profileCode small e z),U),
      ((e.symm s).val,(e.symm t).val))=
      profileCode small e (repairedProfile small B z s.val t.val) := by
  have hc : capacityList (U,(profileCode small e z).1)=
      List.ofFn (fun i => B (e i).val.1 (e i).val.2) := by
    simp only [profileCode,viewList,capacityList_ofFn,hU]
  unfold forwardRepairCode
  rw [hc,crossingIndex_eq]
  change repairedViews (viewList small e z false,
    (List.ofFn (fun i => B (e i).val.1 (e i).val.2),
      ((e.symm t).val,cellIndex small e (t.val.1,s.val.2))))=_
  have ht : cellIndex small e t.val=(e.symm t).val := by
    simp only [cellIndex,t.property,dite_true]
  rw [←ht]
  exact repairedViews_eq small e B z s.val t.val

theorem inverseRepairCode_eq (B : Fin m → Fin n → ℕ) (U : ℕ)
    (hU : ∀ a : Cells small,B a.val.1 a.val.2=U) (z : SmallProfile small)
    (s t : Cells small) :
    inverseRepairCode (((cellCatalog small e,profileCode small e z),U),
      ((e.symm s).val,(e.symm t).val))=
      profileCode small e (inverseRepairProfile small B z s.val t.val) := by
  have hc : capacityList (U,(profileCode small e z).1)=
      List.ofFn (fun i => B (e i).val.1 (e i).val.2) := by
    simp only [profileCode,viewList,capacityList_ofFn,hU]
  unfold inverseRepairCode
  rw [hc,crossingIndex_eq]
  have hs : cellIndex small e s.val=(e.symm s).val := by
    simp only [cellIndex,s.property,dite_true]
  have ht : cellIndex small e t.val=(e.symm t).val := by
    simp only [cellIndex,t.property,dite_true]
  rw [←hs,←ht]
  exact backwardViews_eq small e B z s.val t.val

end
end ContingencyTables.SmallGraphProfiles

end OAI
