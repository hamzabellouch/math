import Mathlib
import OAI.Computability.QuantumFactoring.BitStackListOps
import OAI.Computability.QuantumFactoring.BitStackDivision
import OAI.Computability.QuantumFactoring.BitStackOptions

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type} [DecidableEq α]
def assocLookup (k : α) : List (α×β)→Option β
  | []=>none
  | (a,v)::as=>if k=a then some v else assocLookup k as
def assocStep (x : (α×β)×(α×Option β)) : α×Option β :=
  (x.2.1,if x.2.1=x.1.1 then some x.1.2 else x.2.2)
lemma assocFold_reverse (xs : List (α×β)) (k : α) (o : Option β) :
    xs.reverse.foldl (fun s a=>assocStep (a,s)) (k,o)=
      (k,match assocLookup k xs with | none=>o | some b=>some b) := by
  induction xs with
  | nil=>rfl
  | cons a as ih=>
    rw [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]
    by_cases h:k=a.1 <;> simp [assocStep,assocLookup,h]
lemma assocFold_size (ea : α→List Bool) (eb : β→List Bool)
    (xs : List (α×β)) (s : α×Option β) :
    (prodCode ea (optionCode eb) (xs.foldl (fun s a=>assocStep (a,s)) s)).length≤
      (prodCode ea (optionCode eb) s).length+(listCode (prodCode ea eb) xs).length := by
  induction xs generalizing s with
  | nil=>simp
  | cons a as ih=>
    have hh:=ih (assocStep (a,s))
    have hb : (prodCode ea (optionCode eb) (assocStep (a,s))).length≤
        (prodCode ea (optionCode eb) s).length+2*(prodCode ea eb a).length+2:=by
      unfold assocStep
      split <;> simp only [prodCode,pairBits_length,optionCode,List.length_cons] <;> omega
    simp only [List.foldl_cons,listCode_length_cons]
    omega

namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool}
noncomputable def association (da : α) (db : β)
    (eqp : Procedure (prodCode ea ea) boolCode (fun x=>decide (x.1=x.2))) :
    Procedure (prodCode ea (listCode (prodCode ea eb))) (optionCode eb)
      (fun x=>assocLookup x.1 x.2) := by
  let ent:=prodCode ea eb
  let st:=prodCode ea (optionCode eb)
  let e:=first ent st
  let s:=second ent st
  let key:=(first ea (optionCode eb)).comp s
  let ky:=(first ea eb).comp e
  let value:=(second ea eb).comp e
  let upd:=conditional (eqp.comp (key.pair ky)) ((optionSome eb).comp value)
    ((second ea (optionCode eb)).comp s)
  let step : Procedure (prodCode ent st) st (assocStep (α:=α) (β:=β)):=
    (key.pair upd).congrFun (by intro x; simp only [assocStep,Function.comp_apply,decide_eq_true_eq])
  let fold:=foldList (da,db) step Polynomial.X (by
    intro xs s i
    have hh:=assocFold_size ea eb (xs.take i) s
    have ht:=listCode_length_take_le ent i xs
    simp only [Polynomial.eval_X]
    dsimp only [ent,st] at ht ⊢
    omega)
  let start:=((listReverse ent (da,db)).comp (second ea (listCode ent))).pair
    ((first ea (listCode ent)).pair (constant (prodCode ea (listCode ent)) (optionCode eb) none))
  exact ((second ea (optionCode eb)).comp (fold.comp start)).congrFun (by
    intro x
    change (x.2.reverse.foldl (fun s a=>assocStep (a,s)) (x.1,none)).2=assocLookup x.1 x.2
    rw [assocFold_reverse]
    cases assocLookup x.1 x.2 <;> rfl)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
