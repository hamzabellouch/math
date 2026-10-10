import OAI.Combinatorics.ContingencyTables.Sampling.SmallRepairListProgram
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileCodeEquality

namespace OAI

/-! # Checking inverse repair candidates against their forward image -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def inverseLabelInput (z : LabelledRepairData) : LabelledRepairData :=
  (((z.1.1.1,inverseRepairCode z),z.1.2),z.2)

def inverseLabelInputRealizer : Realizer inverseLabelInput :=
  pair (pair (pair repairDataCatalog inverseRepairCodeRealizer)
    (composition first second)) second

lemma polynomial_inverseLabelInput : PolynomialTime inverseLabelInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_pair polynomial_repairDataCatalog polynomial_inverseRepairCode)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_second

def inverseLabelTest (z : LabelledRepairData) : Bool :=
  repairLabelTest (inverseLabelInput z) &&
    decide (forwardRepairCode (inverseLabelInput z)=z.1.1.2)

def inverseLabelTestRealizer : Realizer inverseLabelTest :=
  composition (pair
    (composition inverseLabelInputRealizer repairLabelTestRealizer)
    (composition (pair (composition inverseLabelInputRealizer forwardRepairCodeRealizer)
      (composition (composition first first) second)) profileCodeEqual)) boolAnd

lemma polynomial_inverseLabelTest : PolynomialTime inverseLabelTestRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_inverseLabelInput polynomial_repairLabelTest)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_inverseLabelInput polynomial_forwardRepairCode)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second)) polynomial_profileCodeEqual)) polynomial_boolAnd

def inverseRepairLabels (z : RepairData) : List (ℕ×ℕ) :=
  (repairPairs z).filter (fun st => inverseLabelTest (z,st))

def inverseRepairLabelsRealizer : Realizer inverseRepairLabels :=
  composition (pair identity repairPairsRealizer) (filterWith inverseLabelTestRealizer)

lemma polynomial_inverseRepairLabels : PolynomialTime inverseRepairLabelsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_repairPairs)
    (polynomial_filterWith polynomial_inverseLabelTest)

def checkedInverseRepairList (z : RepairData) : List (List ℕ×List ℕ) :=
  (inverseRepairLabels z).map (fun st => inverseRepairCode (z,st))

def checkedInverseRepairListRealizer : Realizer checkedInverseRepairList :=
  composition (pair identity inverseRepairLabelsRealizer) (mapWith inverseRepairCodeRealizer)

theorem polynomial_checkedInverseRepairList : PolynomialTime checkedInverseRepairListRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_inverseRepairLabels)
    (polynomial_mapWith polynomial_inverseRepairCode)

theorem checkedInverseRepairList_length (z : RepairData) :
    (checkedInverseRepairList z).length≤z.1.2.1.length^2 := by
  simpa only [checkedInverseRepairList,List.length_map,inverseRepairLabels,repairPairs_length]
    using List.length_filter_le (fun st => inverseLabelTest (z,st)) (repairPairs z)

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

theorem mem_checkedInverseRepairList (B : Fin m → Fin n → ℕ) (U : ℕ)
    (hU : ∀ a : Cells small,B a.val.1 a.val.2=U) (z w : SmallProfile small)
    (hw : ∀ a,w a≤B a.1.val.1 a.1.val.2) :
    profileCode small e w∈checkedInverseRepairList ((cellCatalog small e,profileCode small e z),U) ↔
      ∃ s t : Cells small,
        IsDefect (smallView small w false) (smallQ small B w) s.val t.val ∧
        z=repairedProfile small B w s.val t.val := by
  simp only [checkedInverseRepairList,List.mem_map,inverseRepairLabels,List.mem_filter]
  constructor
  · rintro ⟨⟨i,j⟩,⟨hij,htest⟩,hcode⟩
    have hbounds := (mem_cellPairs _ _ i j).mp hij
    simp only [profileCode,viewList,List.length_ofFn] at hbounds
    let s := e ⟨i,hbounds.1⟩
    let t := e ⟨j,hbounds.2⟩
    have hs : (e.symm s).val=i := by simp only [s,Equiv.symm_apply_apply]
    have ht : (e.symm t).val=j := by simp only [t,Equiv.symm_apply_apply]
    have hd := (Bool.and_eq_true_iff.mp htest).1
    have hf := of_decide_eq_true (Bool.and_eq_true_iff.mp htest).2
    simp only [inverseLabelInput,hcode] at hd hf
    refine ⟨s,t,?_,?_⟩
    · apply (repairLabelTest_iff small e B U hU w (fun a => hw (a,true)) s t).mp
      simpa only [hs,ht] using hd
    · have he := forwardRepairCode_eq small e B U hU w s t
      rw [hs,ht] at he
      exact ((profileCode_injective small e) (he.symm.trans hf)).symm
  · rintro ⟨s,t,hd,hz⟩
    let st := ((e.symm s).val,(e.symm t).val)
    have hc : inverseRepairCode (((cellCatalog small e,profileCode small e z),U),st)=
        profileCode small e w := by
      rw [inverseRepairCode_eq small e B U hU z s t,hz,
        inverseRepairProfile_repaired small B w s.val t.val hw hd]
    refine ⟨st,⟨?_,?_⟩,hc⟩
    · apply (mem_cellPairs _ _ _ _).mpr
      simpa only [profileCode,viewList,List.length_ofFn] using
        And.intro (e.symm s).isLt (e.symm t).isLt
    · simp only [inverseLabelTest,inverseLabelInput,hc,Bool.and_eq_true,decide_eq_true_eq]
      refine ⟨(repairLabelTest_iff small e B U hU w (fun a => hw (a,true)) s t).mpr hd,?_⟩
      exact (forwardRepairCode_eq small e B U hU w s t).trans (congrArg (profileCode small e) hz.symm)

end
end ContingencyTables.SmallGraphProfiles

end OAI
