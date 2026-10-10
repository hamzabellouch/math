import OAI.Combinatorics.ContingencyTables.Sampling.SmallDefectCodeTest

namespace OAI

/-! # Polynomial lists of encoded forward and inverse repairs -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def repairRows : Realizer (fun z : RepairData => z.1.2.1) :=
  composition (composition first second) first

lemma polynomial_repairRowsData : PolynomialTime repairRows :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first

def repairPairs (z : RepairData) : List (ℕ×ℕ) := cellPairs (z.1.2.1,z.1.2.1)

def repairPairsRealizer : Realizer repairPairs :=
  composition (pair repairRows repairRows) cellPairsRealizer

lemma polynomial_repairPairs : PolynomialTime repairPairsRealizer :=
  polynomial_composition (polynomial_pair polynomial_repairRowsData polynomial_repairRowsData)
    polynomial_cellPairs

def forwardRepairLabels (z : RepairData) : List (ℕ×ℕ) :=
  (repairPairs z).filter (fun st => repairLabelTest (z,st))

def forwardRepairLabelsRealizer : Realizer forwardRepairLabels :=
  composition (pair identity repairPairsRealizer) (filterWith repairLabelTestRealizer)

lemma polynomial_forwardRepairLabels : PolynomialTime forwardRepairLabelsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_repairPairs)
    (polynomial_filterWith polynomial_repairLabelTest)

def forwardRepairList (z : RepairData) : List (List ℕ×List ℕ) :=
  (forwardRepairLabels z).map (fun st => forwardRepairCode (z,st))

def forwardRepairListRealizer : Realizer forwardRepairList :=
  composition (pair identity forwardRepairLabelsRealizer) (mapWith forwardRepairCodeRealizer)

theorem polynomial_forwardRepairList : PolynomialTime forwardRepairListRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_forwardRepairLabels)
    (polynomial_mapWith polynomial_forwardRepairCode)

def inverseRepairList (z : RepairData) : List (List ℕ×List ℕ) :=
  (repairPairs z).map (fun st => inverseRepairCode (z,st))

def inverseRepairListRealizer : Realizer inverseRepairList :=
  composition (pair identity repairPairsRealizer) (mapWith inverseRepairCodeRealizer)

theorem polynomial_inverseRepairList : PolynomialTime inverseRepairListRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_repairPairs)
    (polynomial_mapWith polynomial_inverseRepairCode)

lemma repairPairs_length (z : RepairData) : (repairPairs z).length=z.1.2.1.length^2 := by
  simp only [repairPairs,cellPairs,List.length_map,List.length_range,pow_two]

theorem forwardRepairList_length (z : RepairData) :
    (forwardRepairList z).length≤z.1.2.1.length^2 := by
  simpa only [forwardRepairList,List.length_map,forwardRepairLabels,repairPairs_length]
    using List.length_filter_le (fun st => repairLabelTest (z,st)) (repairPairs z)

theorem inverseRepairList_length (z : RepairData) :
    (inverseRepairList z).length=z.1.2.1.length^2 := by
  simp only [inverseRepairList,List.length_map,repairPairs_length]

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

theorem mem_forwardRepairList (B : Fin m → Fin n → ℕ) (U : ℕ)
    (hU : ∀ a : Cells small,B a.val.1 a.val.2=U) (z : SmallProfile small)
    (hb : ∀ a : Cells small,z (a,true)≤B a.val.1 a.val.2) (w : List ℕ×List ℕ) :
    w∈forwardRepairList ((cellCatalog small e,profileCode small e z),U) ↔
      ∃ s t : Cells small,
        IsDefect (smallView small z false) (smallQ small B z) s.val t.val ∧
        w=profileCode small e (repairedProfile small B z s.val t.val) := by
  simp only [forwardRepairList,List.mem_map,forwardRepairLabels,List.mem_filter]
  constructor
  · rintro ⟨⟨i,j⟩,⟨hij,hd⟩,hw⟩
    have hbounds := (mem_cellPairs _ _ i j).mp hij
    simp only [profileCode,viewList,List.length_ofFn] at hbounds
    let si : Fin q := ⟨i,hbounds.1⟩
    let ti : Fin q := ⟨j,hbounds.2⟩
    have hs : e.symm (e si)=si := e.symm_apply_apply si
    have ht : e.symm (e ti)=ti := e.symm_apply_apply ti
    refine ⟨e si,e ti,?_,?_⟩
    · apply (repairLabelTest_iff small e B U hU z hb (e si) (e ti)).mp
      simpa only [hs,ht] using hd
    · rw [←hw]
      simpa only [hs,ht] using forwardRepairCode_eq small e B U hU z (e si) (e ti)
  · rintro ⟨s,t,hd,rfl⟩
    refine ⟨((e.symm s).val,(e.symm t).val),⟨?_,?_⟩,?_⟩
    · apply (mem_cellPairs _ _ _ _).mpr
      simpa only [profileCode,viewList,List.length_ofFn] using
        And.intro (e.symm s).isLt (e.symm t).isLt
    · exact (repairLabelTest_iff small e B U hU z hb s t).mpr hd
    · exact forwardRepairCode_eq small e B U hU z s t

end
end ContingencyTables.SmallGraphProfiles

end OAI
