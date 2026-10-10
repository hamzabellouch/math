import OAI.Combinatorics.ContingencyTables.Sampling.ProfileRepairProgram
import OAI.Combinatorics.ContingencyTables.Sampling.InverseSmallRepair

namespace OAI

/-! # A polynomial binary program for each labelled inverse repair -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

/-- The three indices are the negative cell, positive cell and crossing
cell. A crossing cell outside the small list has its length as index. -/
abbrev InverseRepairInput := List ℕ×(List ℕ×(ℕ×(ℕ×ℕ)))

def backwardRows (z : InverseRepairInput) : List ℕ :=
  listExchange (z.1,(z.2.2.2.1,z.2.2.2.2))

def backwardRowsRealizer : Realizer backwardRows :=
  composition (pair first (composition (composition second second) second)) listExchangeRealizer

lemma polynomial_backwardRows : PolynomialTime backwardRowsRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_second))
    polynomial_listExchange

def backwardColumns (z : InverseRepairInput) : List ℕ :=
  listExchange (backwardRows z,(z.2.2.1,z.2.2.2.1))

def backwardColumnsRealizer : Realizer backwardColumns :=
  composition (pair backwardRowsRealizer (pair
    (composition (composition second second) first)
    (composition (composition (composition second second) second) first))) listExchangeRealizer

lemma polynomial_backwardColumns : PolynomialTime backwardColumnsRealizer :=
  polynomial_composition (polynomial_pair polynomial_backwardRows (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_first)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_second polynomial_second) polynomial_second) polynomial_first)))
    polynomial_listExchange

def backwardViews (z : InverseRepairInput) : List ℕ×List ℕ :=
  (backwardRows z,listDifference (z.2.1,backwardColumns z))

def backwardViewsRealizer : Realizer backwardViews :=
  pair backwardRowsRealizer (composition
    (pair (composition second first) backwardColumnsRealizer) listDifferenceRealizer)

theorem polynomial_backwardViews : PolynomialTime backwardViewsRealizer :=
  polynomial_pair polynomial_backwardRows (polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_second polynomial_first)
      polynomial_backwardColumns) polynomial_listDifference)

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms

noncomputable section
universe u
variable {I J : Type u} [LinearOrder I] [LinearOrder J]
variable (small : I → J → Bool) {n : ℕ} (e : Fin n ≃ Cells small)

private lemma transfer_at_index (X : I → J → ℕ) (s t : I×J) (i : Fin n) :
    (transferInt X s t (e i).val.1 (e i).val.2).toNat=
      X (e i).val.1 (e i).val.2+(if i.val=cellIndex small e t then 1 else 0)-
        (if i.val=cellIndex small e s then 1 else 0) := by
  simp only [cellIndex_eq,Prod.ext_iff,transferInt]
  split_ifs <;> omega

/-- Exactness holds for all input profiles; neither boundedness nor a
preexisting proof of a defect is needed to execute the inverse formula. -/
theorem backwardViews_eq (B : I → J → ℕ) (v : SmallProfile small) (s t : I×J) :
    backwardViews (viewList small e v false,
      (List.ofFn (fun i => B (e i).val.1 (e i).val.2),
        (cellIndex small e s,(cellIndex small e t,cellIndex small e (t.1,s.2)))))=
      (viewList small e (inverseRepairProfile small B v s t) false,
        viewList small e (inverseRepairProfile small B v s t) true) := by
  let w : Fin n → ℕ := fun i => v (e i,false)+
    (if i.val=cellIndex small e t then 1 else 0)-
      (if i.val=cellIndex small e (t.1,s.2) then 1 else 0)
  have hw (i : Fin n) : w i=inverseRepairRow small v s t (e i).val.1 (e i).val.2 := by
    change w i=(transferInt (smallView small v false) (t.1,s.2) t
      (e i).val.1 (e i).val.2).toNat
    have h := transfer_at_index small e (smallView small v false) (t.1,s.2) t i
    have heta : (⟨((e i).val.1,(e i).val.2),(e i).property⟩ : Cells small)=e i :=
      Subtype.ext (Prod.eta (e i).val)
    simpa only [w,smallView,(e i).property,dite_true,heta] using h.symm
  have hq (i : Fin n) :
      w i+(if i.val=cellIndex small e s then 1 else 0)-
        (if i.val=cellIndex small e t then 1 else 0)=
      (transferInt (inverseRepairRow small v s t) t s (e i).val.1 (e i).val.2).toNat := by
    rw [hw]
    exact (transfer_at_index small e (inverseRepairRow small v s t) t s i).symm
  simp only [backwardViews,backwardRows,backwardColumns,viewList,
    listExchange_ofFn_nat,listDifference_ofFn]
  apply Prod.ext
  · apply congrArg List.ofFn
    funext i
    exact hw i
  · apply congrArg List.ofFn
    funext i
    exact congrArg (fun a => B (e i).val.1 (e i).val.2-a) (hq i)

end
end ContingencyTables.SmallGraphProfiles

end OAI
