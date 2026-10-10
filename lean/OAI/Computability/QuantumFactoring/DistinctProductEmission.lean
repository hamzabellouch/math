import Mathlib
import OAI.Computability.QuantumFactoring.DistinctProductCircuit
import OAI.Computability.QuantumFactoring.FirstProperEmission
import OAI.Computability.QuantumFactoring.TableArithmeticEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
namespace NetsEmits
variable {α : Type} {ea : α→List Bool} {k n : α→ℕ}
lemma drop {a : α→ℕ} {ps : ∀x,List (BooleanNetwork (k x) (n x))}
    (ha : Emits ea Nat.bits a) (hp : NetsEmits ea ps) : NetsEmits ea (fun x=>(ps x).drop (a x)):=by
  exact ((ofProcedure (Procedure.listDrop packCode)).comp (ha.pair hp)).congr
    (fun x=>(List.map_drop ..).symm)
end NetsEmits
namespace NetEmits
open BitArithmetic
variable {α : Type} {ea : α→List Bool} {k n K : α→ℕ}
lemma occursLater {p : ∀x,BooleanNetwork (k x) (n x)} {ps : ∀x,List (BooleanNetwork (k x) (n x))}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hp : NetEmits ea p) (hps : NetsEmits ea ps) :
    NetEmits ea (fun x=>BitArithmetic.occursLater (p x) (ps x)):=by
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose (fun x:Σa,Fin ((ps a).length)=>(x.2.val,x.1))
  exact (hps.map (g:=fun x q=>((p x).pair q).comp (BitArithmetic.wordEq (n x)))
    (((hp.compInput hx.snd).pair hps.get).comp (wordEq (hn.comp hx.snd)))).any hk
lemma distinctProductOfFn {f : ∀x,Fin (K x)→BooleanNetwork (k x) (n x)}
    {value : ∀x,BooleanNetwork (k x) (n x)→BooleanNetwork (k x) (n x)}
    (hk : Emits ea unaryCode k) (hn : Emits ea unaryCode n) (hK : Emits ea unaryCode K)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2))
    (hv : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>value x.1 (f x.1 x.2))) :
    NetEmits ea (fun x=>BitArithmetic.distinctProductNet (value x) (List.ofFn (f x))):=by
  let F:=fun x j=>BitArithmetic.distinctProductNet (value x) ((List.ofFn (f x)).drop (K x-j))
  have h0 : NetEmits ea (fun x=>F x 0):=by
    have h:=wordConst hk hn (const _ _ 1)
    exact h.congr (by intro x;dsimp only [F];rw [Nat.sub_zero,List.drop_eq_nil_of_le (by simp)];rfl)
  have hs : NetEmits (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode packCode)
      (x.1,(x.2.val,erasePack (F x.1 x.2.val)))) (fun x=>F x.1 (x.2.val+1)):=by
    have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (K a)=>(x.1,(x.2.val,erasePack (F x.1 x.2.val))))
    let y : (Σa,Fin (K a))→(Σa,Fin (K a)):=fun x=>⟨x.1,⟨K x.1-(x.2.val+1),by have:=x.2.isLt;omega⟩⟩
    have hi:=((hK.comp hx.fst).unaryNat.natSub (hx.snd.fst.unaryNat.natAdd (const _ _ 1))).boundedUnary
      (hK.comp hx.fst) (fun _=>Nat.sub_le _ _)
    have hy : Emits (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode packCode)
        (x.1,(x.2.val,erasePack (F x.1 x.2.val))))
        (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) y:=
      (hi.pair hx.fst).recode (by intros;rfl)
    have htail:=NetsEmits.drop ((hK.comp hx.fst).unaryNat.natSub hx.snd.fst.unaryNat)
      ((NetsEmits.ofFn hK hf).comp hx.fst)
    have hstep:=(((occursLater (hk.comp hx.fst) (hn.comp hx.fst) (hf.compInput (g:=y) hy) htail).wordMux
      (wordConst (hk.comp hx.fst) (hn.comp hx.fst) (const _ _ 1)) (hv.compInput (g:=y) hy) (hn.comp hx.fst)).pair
      (ofCanonical hx.snd.snd)).comp (mul (hn.comp hx.fst))
    convert hstep using 1
    funext x
    dsimp only [F]
    rw [dropOfFn_step _ x.2.isLt,BitArithmetic.distinctProductNet]
    rfl
  obtain ⟨pc,hpc⟩:=countPolyIndexed hK hf
  obtain ⟨pv,hpv⟩:=countPolyIndexed (f:=fun x i=>value x (f x i)) hK hv
  let len:=fun x:Σa,Fin (K a+1)=>(ea x.1).length
  have hC : PolyAt len (fun x=>pc.eval (len x)):=⟨pc,fun _=>le_rfl⟩
  have hV : PolyAt len (fun x=>pv.eval (len x)):=⟨pv,fun _=>le_rfl⟩
  have hW:=hn.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  have hL:=hK.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  have hc : NetworkAt len (fun x=>F x.1 x.2.val):=by
    apply (hL.mul ((((hV.add ((PolyAt.const len 90).mul (hW.pow 2))).add
      ((PolyAt.const len 22).mul hW)).add (PolyAt.const len 7)).add
      (hL.mul (((PolyAt.const len 2).mul hC).add ((PolyAt.const len 96).mul hW) |>.add (PolyAt.const len 25)))) |>.add hW).of_le
    intro x
    have hb:=BitArithmetic.distinctProductNet_count (value x.1) ((List.ofFn (f x.1)).drop (K x.1-x.2.val))
      (c:=pc.eval (len x)) (d:=pv.eval (len x))
      (by intro p hp;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp (List.mem_of_mem_drop hp);exact hpc ⟨x.1,i⟩)
      (by intro p hp;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp (List.mem_of_mem_drop hp);exact hpv ⟨x.1,i⟩)
    dsimp only [F]
    refine hb.trans ?_
    have hlen : ((List.ofFn (f x.1)).drop (K x.1-x.2.val)).length≤K x.1:=by simp only [List.length_drop,List.length_ofFn];omega
    nlinarith [Nat.mul_le_mul_left (2*pc.eval (len x)+96*n x.1+25) hlen,
      Nat.mul_le_mul hlen (Nat.add_le_add_left (Nat.mul_le_mul_right (2*pc.eval (len x)+96*n x.1+25) hlen)
        (pv.eval (len x)+90*n x.1*n x.1+22*n x.1+7))]
  simpa only [F,Nat.sub_self,List.drop_zero] using boundedStages hK h0 hs
    (hk.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)) hW hc
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
