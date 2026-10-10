import OAI.Combinatorics.ContingencyTables.Sampling.ProfileExchangeProgram
import OAI.Combinatorics.ContingencyTables.Sampling.SmallProfileRepair

namespace OAI

/-! # A polynomial binary program for the literal small-profile repair -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def differenceEntry (z : (List ℕ×List ℕ)×ℕ) : ℕ :=
  z.1.1.getD z.2 0-z.1.2.getD z.2 0

def differenceEntryRealizer : Realizer differenceEntry :=
  composition (pair
    (composition (pair (composition first first) second) (getDFast 0))
    (composition (pair (composition first second) second) (getDFast 0))) subtract

lemma polynomial_differenceEntry : PolynomialTime differenceEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_getDFast 0))
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      (polynomial_getDFast 0))) polynomial_subtract

/-- Preserve the second list's length, including malformed inputs. -/
def listDifference (z : List ℕ×List ℕ) : List ℕ :=
  (List.range z.2.length).map (fun i => differenceEntry (z,i))

def listDifferenceRealizer : Realizer listDifference :=
  composition (pair identity (composition (composition second listLength) range))
    (mapWith differenceEntryRealizer)

lemma polynomial_listDifference : PolynomialTime listDifferenceRealizer := by
  have hr : PolynomialTime (composition
      (composition (second (A := List ℕ) (B := List ℕ)) listLength) range) := by
    apply polynomial_boundedRange (polynomial_composition polynomial_second polynomial_listLength) X
    intro z
    simp only [Polynomial.eval_X]
    exact (list_length_le_weight z.2).trans (by rw [weight_prod]; omega)
  exact polynomial_composition (polynomial_pair polynomial_identity hr)
    (polynomial_mapWith polynomial_differenceEntry)

lemma listDifference_ofFn {n : ℕ} (b v : Fin n → ℕ) :
    listDifference (List.ofFn b,List.ofFn v)=List.ofFn (fun i => b i-v i) := by
  apply List.ext_getElem
  · simp only [listDifference,List.length_map,List.length_range,List.length_ofFn]
  · intro a ha _
    have han : a<n := by
      simpa only [listDifference,List.length_map,List.length_range,List.length_ofFn] using ha
    simp only [listDifference,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      differenceEntry,List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa using han),
      List.getElem?_eq_getElem (by simpa using han)]
    simp only [Option.getD_some,List.getElem_ofFn]

/-- Natural indices permit the receiver to be absent from the list. -/
lemma listExchange_ofFn_nat {n : ℕ} (v : Fin n → ℕ) (i j : ℕ) :
    listExchange (List.ofFn v,(i,j))=
      List.ofFn (fun a => v a+(if a.val=i then 1 else 0)-(if a.val=j then 1 else 0)) := by
  apply List.ext_getElem
  · simp only [listExchange,List.length_map,List.length_range,List.length_ofFn]
  · intro a ha _
    have han : a<n := by
      simpa only [listExchange,List.length_map,List.length_range,List.length_ofFn] using ha
    simp only [listExchange,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      exchangeEntry,List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa using han)]
    simp only [Option.getD_some,List.getElem_ofFn]

abbrev RepairInput := List ℕ×(List ℕ×(ℕ×ℕ))

/-- The final pair stores the source and receiver respectively. -/
def repairedViews (z : RepairInput) : List ℕ×List ℕ :=
  let w := listExchange (z.1,(z.2.2.2,z.2.2.1))
  (w,listDifference (z.2.1,w))

def repairRowsRealizer : Realizer (fun z : RepairInput =>
    listExchange (z.1,(z.2.2.2,z.2.2.1))) :=
  composition (pair first (pair
    (composition (composition second second) second)
    (composition (composition second second) first))) listExchangeRealizer

lemma polynomial_repairRows : PolynomialTime repairRowsRealizer :=
  polynomial_composition (polynomial_pair polynomial_first (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_first)))
    polynomial_listExchange

def repairedViewsRealizer : Realizer repairedViews :=
  pair repairRowsRealizer (composition
    (pair (composition second first) repairRowsRealizer) listDifferenceRealizer)

theorem polynomial_repairedViews : PolynomialTime repairedViewsRealizer :=
  polynomial_pair polynomial_repairRows (polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_second polynomial_first) polynomial_repairRows)
    polynomial_listDifference)

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles
open ProfilePrograms

noncomputable section
universe u
variable {I J : Type u} [LinearOrder I] [LinearOrder J]
variable (small : I → J → Bool) {n : ℕ} (e : Fin n ≃ Cells small)

/-- An absent large cell receives the out-of-range code `n`. -/
def cellIndex (t : I×J) : ℕ :=
  if h : small t.1 t.2=true then (e.symm ⟨t,h⟩).val else n

omit [LinearOrder I] [LinearOrder J] in
lemma cellIndex_eq (i : Fin n) (t : I×J) :
    i.val=cellIndex small e t ↔ (e i).val=t := by
  unfold cellIndex
  split_ifs with ht
  · constructor
    · intro h
      have hi : i=e.symm ⟨t,ht⟩ := Fin.ext h
      rw [hi,Equiv.apply_symm_apply]
    · intro h
      have he : e i=⟨t,ht⟩ := Subtype.ext h
      have hi := congrArg e.symm he
      simpa only [Equiv.symm_apply_apply] using congrArg Fin.val hi
  · constructor
    · intro h
      exact False.elim (Nat.ne_of_lt i.isLt h)
    · intro h
      exact False.elim (ht (h ▸ (e i).property))

def viewList (v : SmallProfile small) (b : Bool) : List ℕ :=
  List.ofFn (fun i => v (e i,b))

private lemma indexed_transfer (v : SmallProfile small) (s t : I×J) (i : Fin n) :
    (transferInt (smallView small v false) s t (e i).val.1 (e i).val.2).toNat=
      v (e i,false)+(if i.val=cellIndex small e t then 1 else 0)-
        (if i.val=cellIndex small e s then 1 else 0) := by
  have heta : (⟨((e i).val.1,(e i).val.2),(e i).property⟩ : Cells small)=e i :=
    Subtype.ext (Prod.eta (e i).val)
  simp only [cellIndex_eq]
  simp only [Prod.ext_iff,transferInt,smallView,(e i).property,dite_true,heta]
  split_ifs <;> omega

/-- The executable row transfer and complement produce exactly the
graph repair, including a large crossing cell outside the stored list. -/
theorem repairedViews_eq (B : I → J → ℕ) (v : SmallProfile small) (s t : I×J) :
    repairedViews (viewList small e v false,
      (List.ofFn (fun i => B (e i).val.1 (e i).val.2),
        (cellIndex small e t,cellIndex small e (t.1,s.2))))=
      (viewList small e (repairedProfile small B v s t) false,
        viewList small e (repairedProfile small B v s t) true) := by
  let w : Fin n → ℕ := fun i => v (e i,false)+
    (if i.val=cellIndex small e (t.1,s.2) then 1 else 0)-
      (if i.val=cellIndex small e t then 1 else 0)
  have hw (i : Fin n) : w i=repairMatrix (smallView small v false) s t (e i).val.1 (e i).val.2 :=
    (indexed_transfer small e v t (t.1,s.2) i).symm
  simp only [repairedViews,viewList,listExchange_ofFn_nat,listDifference_ofFn]
  apply Prod.ext
  · apply congrArg List.ofFn
    funext i
    exact hw i
  · apply congrArg List.ofFn
    funext i
    exact congrArg (fun a => B (e i).val.1 (e i).val.2-a) (hw i)

end
end ContingencyTables.SmallGraphProfiles

end OAI
