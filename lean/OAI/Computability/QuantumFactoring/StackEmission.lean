import Mathlib
import OAI.Computability.QuantumFactoring.PrimalityEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {k s w : α→ℕ}
lemma stackPop (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) :
    NetEmits ea (fun x=>BitArithmetic.stackPop (s x) (w x)):=by
  unfold BitArithmetic.stackPop
  apply wordBlocks (hs.unaryMul hw) hs hw
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (s a)=>(x.2.val,x.1))
  have hS:=hs.comp hx.snd
  have hW:=hw.comp hx.snd
  apply splitOn (fun x=>x.2.val+1<s x.1) (hx.fst.unarySucc.unaryNat.natLt hS.unaryNat)
  · let inc : {x : Σa,Fin (s a) // x.2.val+1<s x.1} → (Σa,Fin (s a)) := Subtype.val
    have hb:=blockNet (hS.precompose inc) (hW.precompose inc)
      (fun x=>⟨x.val.2.val+1,x.property⟩) (hx.fst.unarySucc.unaryNat.precompose inc)
    exact hb.congr (by intro x;rw [dite_eq_left x.property])
  · let inc : {x : Σa,Fin (s a) // ¬x.2.val+1<s x.1} → (Σa,Fin (s a)) := Subtype.val
    have hz:=wordConst ((hS.unaryMul hW).precompose inc) (hW.precompose inc) (const _ _ 0)
    exact hz.congr (by intro x;rw [dite_eq_right x.property];rfl)
lemma stackPush {a : ∀x,BooleanNetwork (k x) (w x)} {v : ∀x,BooleanNetwork (k x) (s x*w x)}
    (hk : Emits ea unaryCode k) (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    (ha : NetEmits ea a) (hv : NetEmits ea v) :
    NetEmits ea (fun x=>BitArithmetic.stackPush (a x) (v x)):=by
  unfold BitArithmetic.stackPush
  apply wordBlocks hk hs hw
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (s a)=>(x.2.val,x.1))
  apply splitOn (fun x=>x.2.val=0) (hx.fst.unaryNat.natEq (const _ _ 0))
  · exact ((ha.compInput hx.snd).precompose Subtype.val).congr (by intro x;rw [dite_eq_left x.property])
  · let inc : {x : Σa,Fin (s a) // ¬x.2.val=0} → (Σa,Fin (s a)) := Subtype.val
    have hb:=blockNet ((hs.comp hx.snd).precompose inc) ((hw.comp hx.snd).precompose inc)
      (fun x=>⟨x.val.2.val-1,by dsimp only [inc];have:=x.val.2.isLt;omega⟩)
      ((hx.fst.unaryNat.natSub (const _ _ 1)).precompose inc)
    exact (((hv.compInput hx.snd).precompose inc).comp hb).congr (by intro x;rw [dite_eq_right x.property])
lemma primeWord (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.primeWord (w x)):=
  ((wordConst hw hw (const _ _ 2)).wordLe (identity hw) hw).band
    ((resize hw (hw.unaryMul hw).unarySucc).comp (primality hw))
end ExactQuantumFactoring.NetworkEmission.NetEmits

end


end OAI
