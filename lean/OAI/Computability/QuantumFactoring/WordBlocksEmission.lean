import Mathlib
import OAI.Computability.QuantumFactoring.NetworkModularEmission
import OAI.Computability.QuantumFactoring.NetworkSequenceEmission
import OAI.Computability.QuantumFactoring.EmissionPolynomialUnary

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
lemma result {f : α→β} {g : α→γ} (hf : Emits ea eb f) (h : ∀x,eb (f x)=ec (g x)) :
    Emits ea ec g:=by
  obtain ⟨p⟩:=hf
  exact ⟨p.result h⟩
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n s w : α→ℕ}
lemma blockNet (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    (i : ∀x,Fin (s x)) (hi : Emits ea Nat.bits (fun x=>(i x).val)) :
    NetEmits ea (fun x=>BitArithmetic.blockNet (s x) (w x) (i x)):=
  selectSlice (hs.unaryMul hw) hw (hw.unaryNat.natMul hi) _ (by intro x j;change j.val+w x*(i x).val=w x*(i x).val+j.val;omega)
lemma wordBlocks {f : ∀x,Fin (s x)→BooleanNetwork (n x) (w x)}
    (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    (hf : NetEmits (fun x:Σx,Fin (s x)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.wordBlocks (f x)):=by
  let eb:=fun x:Σx,Fin (s x*w x)=>prodCode unaryCode ea (x.2.val,x.1)
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σx,Fin (s x*w x)=>(x.2.val,x.1))
  have hW:=hw.comp hx.snd
  have hI:=hx.fst.unaryNat
  have hdiv:= (hI.natDiv hW.unaryNat).boundedUnary hx.fst (by intro x;exact Nat.div_le_self _ _)
  have harg : Emits eb (fun x:Σx,Fin (s x)=>prodCode unaryCode ea (x.2.val,x.1))
      (fun x=>⟨x.1,(finProdFinEquiv.symm x.2).1⟩):=
    (hdiv.pair hx.snd).result (by intro x;rfl)
  have hF:=hf.input harg
  have ho:=hI.natMod hW.unaryNat
  have hb:=hF.rewireSlice (const _ _ 1) ho (fun x _=>(finProdFinEquiv.symm x.2).2)
    (by
      intro x i
      change x.2.val % w x.1 = x.2.val % w x.1 + i.val
      have := i.isLt
      omega)
  exact vectorOfFn hn (hs.unaryMul hw) hb
lemma arrayConstant {f : ∀x,Fin (s x)→ℕ}
    (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    (hf : Emits (fun x:Σx,Fin (s x)=>prodCode unaryCode ea (x.2.val,x.1)) Nat.bits (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.arrayConstant (n:=n x) (s x) (w x) (f x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σx,Fin (s x)=>(x.2.val,x.1))
  exact wordBlocks hn hs hw (wordConst (hn.comp hx.snd) (hw.comp hx.snd) hf)
lemma addMod {a b m : ∀x,BooleanNetwork (n x) (w x)}
    (ha : NetEmits ea a) (hb : NetEmits ea b) (hm : NetEmits ea m) (hw : Emits ea unaryCode w) :
    NetEmits ea (fun x=>BitArithmetic.addMod (a x) (b x) (m x)):=by
  have hp:=padRight hw (const _ _ 1)
  exact (((((ha.comp hp).pair (hb.comp hp)).comp (add hw.unarySucc)).pair
    (hm.comp hp)).comp (mod hw.unarySucc)).rewireSlice hw (const _ _ 0)
      (fun _=>Fin.castAdd 1) (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
