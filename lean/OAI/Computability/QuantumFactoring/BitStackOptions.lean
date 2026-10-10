import Mathlib
import OAI.Computability.QuantumFactoring.BitStackBooleans
import OAI.Computability.QuantumFactoring.BitStackListCode
import OAI.Computability.QuantumFactoring.Procedure

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}
def optionCode (ea : α→List Bool) : Option α→List Bool
  | none=>[false]
  | some a=>true::ea a
def optionView : Option α→Unit⊕α
  | none=>.inl ()
  | some a=>.inr a
lemma optionCode_length_some (ea : α→List Bool) (a : α) :
    (optionCode ea (some a)).length=(ea a).length+1 := rfl

namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool}
noncomputable def optionSome (ea : α→List Bool) : Procedure ea (optionCode ea) some :=
  (prepend ea [true]).result (by intro a;rfl)
noncomputable def optionCases {f : Unit→β} {g : α→β}
    (p : Procedure emptyCode eb f) (q : Procedure ea eb g) :
    Procedure (optionCode ea) eb (fun x=>Sum.elim f g (optionView x)) :=
  ((casesSum p q).precompose optionView).congrEncoding
    (by intro x;cases x <;> rfl) (by intro x;rfl)
noncomputable def optionGet (ea : α→List Bool) (d : α) :
    Procedure (optionCode ea) ea (fun x=>x.getD d) :=
  (optionCases (constant emptyCode ea d) (identity ea)).congrFun
    (by intro x;cases x <;> rfl)
noncomputable def optionIsSome (ea : α→List Bool) :
    Procedure (optionCode ea) boolCode Option.isSome :=
  (optionCases (constant emptyCode boolCode false) (constant ea boolCode true)).congrFun
    (by intro x;cases x <;> rfl)
noncomputable def binaryEq : Procedure (prodCode Nat.bits Nat.bits) boolCode
    (fun x=>decide (x.1=x.2)) := by
  let swap:=(second Nat.bits Nat.bits).pair (first Nat.bits Nat.bits)
  exact (boolAnd.comp (binaryLe.pair (binaryLe.comp swap))).congrFun
    (by intro x;apply Bool.eq_iff_iff.mpr;simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq];omega)
noncomputable def prodEq [DecidableEq α] [DecidableEq β]
    (pa : Procedure (prodCode ea ea) boolCode (fun x=>decide (x.1=x.2)))
    (pb : Procedure (prodCode eb eb) boolCode (fun x=>decide (x.1=x.2))) :
    Procedure (prodCode (prodCode ea eb) (prodCode ea eb)) boolCode
      (fun x=>decide (x.1=x.2)) := by
  let l:=first (prodCode ea eb) (prodCode ea eb)
  let r:=second (prodCode ea eb) (prodCode ea eb)
  let a:=pa.comp (((first ea eb).comp l).pair ((first ea eb).comp r))
  let b:=pb.comp (((second ea eb).comp l).pair ((second ea eb).comp r))
  exact (boolAnd.comp (a.pair b)).congrFun (by rintro ⟨⟨a,b⟩,⟨c,d⟩⟩;apply Bool.eq_iff_iff.mpr;simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,Prod.mk.injEq])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end

end OAI
