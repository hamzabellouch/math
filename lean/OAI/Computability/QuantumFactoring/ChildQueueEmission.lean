import Mathlib
import OAI.Computability.QuantumFactoring.ChildQueueBounds
import OAI.Computability.QuantumFactoring.FirstProperEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
lemma dropOfFn_eq {β : Type} {K : ℕ} (f : Fin K→β) (d : ℕ) :
    (List.ofFn f).drop d=List.ofFn (fun i:Fin (K-d)=>f ⟨d+i.val,by have:=i.isLt;omega⟩):=by
  apply List.ext_getElem
  · simp only [List.length_drop,List.length_ofFn]
  · intro i h h'
    simp only [List.getElem_drop,List.getElem_ofFn]
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {k w K s : α→ℕ}
lemma wordMemberOfFn {a : ∀x,BooleanNetwork (k x) (w x)} {f : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (ha : NetEmits ea a)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.ChildQueue.wordMember (a x) (List.ofFn (f x))):=by
  simp only [BitArithmetic.ChildQueue.wordMember,List.map_ofFn]
  apply anyOfFn hk hK
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (K a)=>(x.2.val,x.1))
  exact ((ha.compInput hx.snd).pair hf).comp (wordEq (hw.comp hx.snd))
lemma wordMemberDrop {a : ∀x,BooleanNetwork (k x) (w x)} {f : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    {d : α→ℕ} (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hd : Emits ea Nat.bits d) (ha : NetEmits ea a)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.ChildQueue.wordMember (a x) ((List.ofFn (f x)).drop (d x))):=by
  have len:=(hK.unaryNat.natSub hd).boundedUnary hK (fun _=>Nat.sub_le _ _)
  have hh : NetEmits ea (fun x=>BitArithmetic.ChildQueue.wordMember (a x)
      (List.ofFn (fun i:Fin (K x-d x)=>f x ⟨d x+i.val,by have:=i.isLt;omega⟩))):=by
    apply wordMemberOfFn hk hw len ha
    have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
      (fun x:Σa,Fin (K a-d a)=>(x.2.val,x.1))
    let inc:(Σa,Fin (K a-d a))→(Σa,Fin (K a)):=fun x=>⟨x.1,⟨d x.1+x.2.val,by have:=x.2.isLt;omega⟩⟩
    have hi:=((hd.comp hx.snd).natAdd hx.fst.unaryNat).boundedUnary (hK.comp hx.snd) (by
      intro x;dsimp only;have:=x.2.isLt;omega)
    exact hf.compInput ((hi.pair hx.snd).recode (by intros;rfl) : Emits _ _ inc)
  exact hh.congr (fun x=>by rw [dropOfFn_eq])
lemma childPushOneDrop {a : ∀x,BooleanNetwork (k x) (w x)} {f : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    {d : α→ℕ} (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hs : Emits ea unaryCode s) (hd : Emits ea Nat.bits d) (ha : NetEmits ea a)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.ChildQueue.pushOne (s x) (a x) ((List.ofFn (f x)).drop (d x))):=by
  have hsource:=left hk (hs.unaryMul hw)
  have hqueue:=right hk (hs.unaryMul hw)
  have hwidth:=hk.unaryAdd (hs.unaryMul hw)
  have active:=((wordConst hk hw (const _ _ 2)).wordLt ha hw).band (wordMemberDrop hk hw hK hd ha hf).bnot
  exact hsource.pair ((hsource.comp active).wordMux
    (stackPush hwidth hs hw (((hsource.comp ha).pair (wordConst hwidth hw (const _ _ 1))).comp (sub hw)) hqueue) hqueue (hs.unaryMul hw))
lemma childPushAll {f : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hs : Emits ea unaryCode s)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.ChildQueue.pushAll (s x) (List.ofFn (f x))):=by
  let F:=fun x j=>BitArithmetic.ChildQueue.pushAll (s x) ((List.ofFn (f x)).drop (K x-j))
  have h0 : NetEmits ea (fun x=>F x 0):=by
    refine (identity (hk.unaryAdd (hs.unaryMul hw))).congr ?_
    intro x
    dsimp only [F]
    rw [Nat.sub_zero,List.drop_eq_nil_of_le (by simp only [List.length_ofFn];exact le_rfl)]
    rfl
  have step : NetEmits (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode packCode)
      (x.1,(x.2.val,erasePack (F x.1 x.2.val)))) (fun x=>F x.1 (x.2.val+1)):=by
    have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (K a)=>(x.1,(x.2.val,erasePack (F x.1 x.2.val))))
    have hLen:=hK.comp hx.fst
    let y : (Σa,Fin (K a))→(Σa,Fin (K a)):=fun x=>⟨x.1,⟨K x.1-(x.2.val+1),by have:=x.2.isLt;omega⟩⟩
    have hi:=(hLen.unaryNat.natSub (hx.snd.fst.unaryNat.natAdd (const _ _ 1))).boundedUnary hLen (fun _=>Nat.sub_le _ _)
    have hy : Emits _ (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) y:=
      (hi.pair hx.fst).recode (by intros;rfl)
    have hfields : NetEmits (fun z:Σx:Σa,Fin (K a),Fin (K x.1)=>prodCode unaryCode
        (fun x:Σa,Fin (K a)=>prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.val,erasePack (F x.1 x.2.val)))) (z.2.val,z.1))
        (fun z=>f z.1.1 z.2):=by
      have hz:=(BitStackProgram.Emits.id (prodCode unaryCode (prodCode ea (prodCode unaryCode packCode)))).precompose
        (fun z:Σx:Σa,Fin (K a),Fin (K x.1)=>(z.2.val,(z.1.1,(z.1.2.val,erasePack (F z.1.1 z.1.2.val)))))
      exact hf.compInput ((hz.fst.pair hz.snd.fst).recode (g:=fun z:Σx:Σa,Fin (K a),Fin (K x.1)=>(⟨z.1.1,z.2⟩ : Σa,Fin (K a))) (by intros;rfl))
    have hnew:=(ofCanonical hx.snd.snd).comp (childPushOneDrop (f:=fun x=>f x.1) (a:=fun x=>f (y x).1 (y x).2) (hk.comp hx.fst) (hw.comp hx.fst)
      hLen (hs.comp hx.fst) (hLen.unaryNat.natSub hx.snd.fst.unaryNat) (hf.compInput hy) hfields)
    convert hnew using 1
    funext x
    dsimp only [F]
    rw [dropOfFn_step _ x.2.isLt,BitArithmetic.ChildQueue.pushAll]
  have hwidth:=(hk.unaryPoly.add (hs.unaryPoly.mul hw.unaryPoly)).pull (fun x:Σa,Fin (K a+1)=>x.1)
  obtain ⟨p,hp⟩:=countPolyIndexed hK hf
  have hc : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>p.eval (ea x.1).length):=⟨p,fun _=>le_rfl⟩
  have hS:=hs.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  have hW:=hw.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  have hL:=hK.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  have hone:=(((hc.add ((PolyAt.const _ 49).mul hW)).add (PolyAt.const _ 11)).add
    (hL.mul ((((PolyAt.const _ 2).mul hc).add ((PolyAt.const _ 96).mul hW)).add (PolyAt.const _ 25)))).add
    ((hS.mul hW).mul ((hc.add ((PolyAt.const _ 159).mul hW)).add (PolyAt.const _ 6))) |>.add
      ((PolyAt.const _ 7).mul (hS.mul hW))
  have hb : NetworkAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>F x.1 x.2.val):=by
    exact (hL.mul hone).of_le (by
      intro x
      have h:=BitArithmetic.ChildQueue.pushAll_count (s x.1) ((List.ofFn (f x.1)).drop (K x.1-x.2.val))
        (c:=p.eval (ea x.1).length) (by
          intro b hb
          obtain ⟨i,rfl⟩:=List.mem_ofFn.mp (List.mem_of_mem_drop hb)
          exact hp ⟨x.1,i⟩)
      have hl:((List.ofFn (f x.1)).drop (K x.1-x.2.val)).length≤K x.1:=by
        simp only [List.length_drop,List.length_ofFn];omega
      exact h.trans (Nat.mul_le_mul hl (BitArithmetic.ChildQueue.oneBound_mono _ _ _ hl)))
  simpa only [F,Nat.sub_self,List.drop_zero] using boundedStages hK h0 step hwidth hwidth hb
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
