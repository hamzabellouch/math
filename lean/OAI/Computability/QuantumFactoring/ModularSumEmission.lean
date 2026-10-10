import Mathlib
import OAI.Computability.QuantumFactoring.EmissionLengthBounds
import OAI.Computability.QuantumFactoring.NetworkRecursionEmission

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits BitArithmetic
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {n w k : α→ℕ}
lemma sumModOfFn {m : ∀x,BooleanNetwork (n x) (w x)}
    {f : ∀x,Fin (k x)→BooleanNetwork (n x) (w x)}
    (hn : Emits ea unaryCode n) (hw : Emits ea unaryCode w) (hk : Emits ea unaryCode k)
    (hm : NetEmits ea m)
    (hf : NetEmits (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>sumMod (m x) (List.ofFn (f x))):=by
  let F:=fun x j=>sumMod (m x) ((List.ofFn (f x)).drop (k x-j))
  have h0 : NetEmits ea (fun x=>F x 0):=
    (wordConst hn hw (const _ _ 0)).congr (by
      intro x
      change wordConstant _=sumMod _ ((List.ofFn (f x)).drop (k x-0))
      have hd : (List.ofFn (f x)).drop (k x-0)=[]:=by
        apply List.drop_eq_nil_iff.mpr
        simp only [List.length_ofFn,Nat.sub_zero,le_refl]
      rw [hd];rfl)
  have hs : NetEmits
      (fun x:Σa,Fin (k a)=>prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.val,erasePack (F x.1 x.2.val))))
      (fun x=>F x.1 (x.2.val+1)):=by
    have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (k a)=>(x.1,(x.2.val,erasePack (F x.1 x.2.val))))
    have hi:=((hk.comp hx.fst).unaryNat.natSub hx.snd.fst.unarySucc.unaryNat).boundedUnary
      (hk.comp hx.fst) (by intro x;exact Nat.sub_le _ _)
    let ix:=fun x:Σa,Fin (k a)=>(⟨k x.1-(x.2.val+1),by have:=x.2.isLt;omega⟩ : Fin (k x.1))
    have he : Emits _ (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1))
        (fun x=>⟨x.1,ix x⟩):=
      (hi.pair hx.fst).result (by intro x;rfl)
    have ha:=hf.input he
    have hb:=ofCanonical hx.snd.snd
    have hadd:=addMod ha hb (hm.input hx.fst) (hw.comp hx.fst)
    exact hadd.congr (by
      intro x
      dsimp only [F,ix]
      have hlt : k x.1-(x.2.val+1)<(List.ofFn (f x.1)).length:=by simpa only [List.length_ofFn] using (show k x.1-(x.2.val+1)<k x.1 by have:=x.2.isLt;omega)
      rw [List.drop_eq_getElem_cons hlt]
      simp only [sumMod,List.getElem_ofFn]
      have hlen : (List.ofFn (f x.1)).length=k x.1:=List.length_ofFn
      have := x.2.isLt
      congr 3
      all_goals omega)
  have hcp:=countPolyIndexed hk hf
  obtain ⟨p,hp⟩:=hcp
  let len:=fun x:Σa,Fin (k a+1)=>(ea x.1).length
  have hwP:=hw.unaryPoly.pull (fun x:Σa,Fin (k a+1)=>x.1)
  have hkP:=hk.unaryPoly.pull (fun x:Σa,Fin (k a+1)=>x.1)
  have hmP:=hm.countPoly.pull (fun x:Σa,Fin (k a+1)=>x.1)
  have hpP : PolyAt len (fun x=>p.eval (ea x.1).length):=⟨p,fun _=>le_rfl⟩
  have hwp:=hwP.add (PolyAt.const _ 1)
  have hbound : NetworkAt len (fun x:Σa,Fin (k a+1)=>F x.1 x.2.val):=by
    apply (hwP.add (hkP.mul (((((hpP.add hmP).add ((PolyAt.const _ 216).mul (hwp.pow 2))).add
      ((PolyAt.const _ 142).mul hwp)).add (PolyAt.const _ 15))))).of_le
    intro x
    have h:=sumMod_count (m x.1) ((List.ofFn (f x.1)).drop (k x.1-x.2.val)) (c:=p.eval (ea x.1).length) (by
      intro a ha
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp (List.mem_of_mem_drop ha)
      exact hp ⟨x.1,i⟩)
    have hlen : ((List.ofFn (f x.1)).drop (k x.1-x.2.val)).length≤k x.1:=by
      simp only [List.length_drop,List.length_ofFn];omega
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hlen) _)
  exact (boundedStages hk h0 hs (hn.unaryPoly.pull (fun x:Σa,Fin (k a+1)=>x.1)) hwP hbound).congr
    (by intro x;simp only [F,Nat.sub_self,List.drop_zero])
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end

end OAI
