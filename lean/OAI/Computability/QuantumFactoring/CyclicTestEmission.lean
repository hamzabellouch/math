import Mathlib
import OAI.Computability.QuantumFactoring.CyclicPowerEmission

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}
lemma ofFnNat (d : β) {k : α→ℕ} {f : α→ℕ→β}
    (hk : Emits ea unaryCode k) (hf : Emits (prodCode unaryCode ea) eb (fun x=>f x.2 x.1)) :
    Emits ea (listCode eb) (fun x=>List.ofFn (fun i:Fin (k x)=>f x i.val)):=by
  obtain ⟨p⟩:=hf
  exact ((ofProcedure (Procedure.tabulate (f:=f) d p)).comp (hk.pair (id ea))).congr
    (by intro x;exact (NetworkEmission.ofFn_nat_eq_map _ _).symm)
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits BitArithmetic
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n s w a : α→ℕ}
lemma reverseWord {f : ∀x,BooleanNetwork (n x) (w x)} (hf : NetEmits ea f)
    (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>(f x).rewire Fin.rev):=by
  have hx:=BitStackProgram.Emits.id (prodCode unaryCode ea)
  have hi:=(hw.comp hx.snd).unaryNat.natSub hx.fst.unarySucc.unaryNat
  exact hf.rewire _ (ofFnNat (eb:=Nat.bits) (f:=fun x i=>w x-(i+1)) 0 hw hi)
lemma cyclicX (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    [∀x,NeZero (s x)] : NetEmits ea (fun x=>cyclicXNet (n:=n x) (s x) (w x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (s a)=>(x.2.val,x.1))
  have hc:=hx.fst.unaryNat.natEq ((const _ _ 1).natMod (hs.comp hx.snd).unaryNat)
  apply arrayConstant hn hs hw
  exact (hc.ite (const _ _ 1) (const _ _ 0)).congr (by intro x;simp only [Fin.ext_iff,Fin.val_one',decide_eq_true_eq])
lemma cyclicC (hn : Emits ea unaryCode n) (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w)
    (ha : Emits ea Nat.bits a) [∀x,NeZero (s x)] : NetEmits ea (fun x=>cyclicCNet (n:=n x) (s x) (w x) (a x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (s a)=>(x.2.val,x.1))
  have hc:=hx.fst.unaryNat.natEq (const _ _ 0)
  apply arrayConstant hn hs hw
  exact (hc.ite (ha.comp hx.snd) (const _ _ 0)).congr (by intro x;simp only [Fin.ext_iff,Fin.val_zero,decide_eq_true_eq])
lemma cyclicPowerOn {b : α→ℕ} {f : ∀x,BooleanNetwork (n x) (s x*w x)}
    {m : ∀x,BooleanNetwork (n x) (w x)} {e : ∀x,BooleanNetwork (n x) (b x)}
    [∀x,NeZero (s x)] (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b)
    (hf : NetEmits ea f) (hm : NetEmits ea m) (he : NetEmits ea e) :
    NetEmits ea (fun x=>BitArithmetic.cyclicPowerOn (f x) (m x) (e x)):=
  ((hf.pair hm).pair he).comp (cyclicPower hs hw hb)
lemma cyclicTest (hs : Emits ea unaryCode s) (hw : Emits ea unaryCode w) (ha : Emits ea Nat.bits a)
    [∀x,NeZero (s x)] : NetEmits ea (fun x=>BitArithmetic.cyclicTest (s x) (w x) (a x)):=by
  have hm:=identity hw
  have he:=hm.reverseWord hw
  have hX:=cyclicX hw hs hw
  have hC:=cyclicC hw hs hw ha
  have hl:=cyclicPowerOn hs hw hw (cyclicAdd hw hs hw hX hC hm) hm he
  have hr:=cyclicAdd hw hs hw (cyclicPowerOn hs hw hw hX hm he) hC hm
  exact hl.equalOn hr (hs.unaryMul hw)
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
