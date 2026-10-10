import Mathlib
import OAI.Computability.QuantumFactoring.NetworkExpressionEmission
import OAI.Computability.QuantumFactoring.ExpressionPredicates

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure BitStackProgram.Emits
namespace Emission
noncomputable def swapIndicesP : Procedure unaryCode (listCode Nat.bits)
    (fun w=>List.ofFn (fun i:Fin (w+w)=>(Fin.addCases (Fin.natAdd w) (Fin.castAdd w) i : Fin (w+w)).val)):=by
  let step:=binaryAdd.comp ((unaryToBits.comp (second unaryCode unaryCode)).pair
    (unaryToBits.comp (first unaryCode unaryCode)))
  let a:=(tabulate (f:=fun w i=>w+i) 0 step).comp ((identity unaryCode).pair (identity unaryCode))
  let b:=(tabulate (f:=fun (_:ℕ) i=>i) 0 (unaryToBits.comp (first unaryCode unaryCode))).comp
    ((identity unaryCode).pair (identity unaryCode))
  exact ((Procedure.listAppend Nat.bits 0).comp (a.pair b)).congrFun (by
    intro w
    change (List.range w).map (fun i=>w+i)++(List.range w).map id=_
    rw [←ofFn_val_range,List.map_ofFn,List.map_id,List.ofFn_add]
    congr 1 <;> apply congrArg List.ofFn <;> funext i
    · change w+i.val=(Fin.addCases (Fin.natAdd w) (Fin.castAdd w) (i.castAdd w) : Fin (w+w)).val
      rw [Fin.addCases_left];rfl
    · rw [Fin.addCases_right];rfl)
end Emission
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n w : α→ℕ}
lemma ult (hw : BitStackProgram.Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.ult (w x)):=
  ⟨fun x=>AIGNetworkEmission.ultPack (w x),(ofProcedure AIGNetworkEmission.Emission.ultPackP).comp hw,
    fun x=>AIGNetworkEmission.ultPack_value (w x)⟩
lemma wordEq (hw : BitStackProgram.Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.wordEq (w x)):=by
  have hs : NetEmits ea (fun x=>BooleanNetwork.select
      (Fin.addCases (Fin.natAdd (w x)) (Fin.castAdd (w x)))):=
    select (hw.unaryAdd hw) _ ((ofProcedure Emission.swapIndicesP).comp hw)
  exact ((ult hw).bor (hs.comp (ult hw))).bnot
lemma equalOn {f g : ∀x,BooleanNetwork (n x) (w x)}
    (hf : NetEmits ea f) (hg : NetEmits ea g) (hw : BitStackProgram.Emits ea unaryCode w) :
    NetEmits ea (fun x=>BitArithmetic.equalOn (f x) (g x)):=(hf.pair hg).comp (wordEq hw)
lemma isOne {k : ℕ} {b : α→ℕ} {e : α→NatExpr (Fin k)}
    (he : BitStackProgram.Emits ea (exprCode (fun i:Fin k=>i.val.bits)) e)
    (hn : BitStackProgram.Emits ea unaryCode n) (hb : BitStackProgram.Emits ea unaryCode b)
    {fs : ∀x,Fin k→BooleanNetwork (n x) (b x)} (hf : ∀i,NetEmits ea (fun x=>fs x i)) :
    NetEmits ea (fun x=>(e x).isOne (fs x)):=by
  have hw : BitStackProgram.Emits ea unaryCode (fun x=>(e x).templateWidth (b x)):=
    (ofProcedure (Emission.exprWidthP _)).comp (hb.pair he)
  exact (template he hn hb hf).equalOn (wordConst hn hw (const _ _ 1)) hw
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end


end OAI
