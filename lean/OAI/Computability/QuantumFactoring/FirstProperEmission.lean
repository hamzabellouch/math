import Mathlib
import OAI.Computability.QuantumFactoring.SplitDecoderPolynomial
import OAI.Computability.QuantumFactoring.DescendingFilterEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
lemma dropOfFn_step {β : Type} {K j : ℕ} (f : Fin K→β) (hj : j<K) :
    (List.ofFn f).drop (K-(j+1))=f ⟨K-(j+1),by omega⟩ :: (List.ofFn f).drop (K-j):=by
  rw [List.drop_eq_getElem_cons (by simp only [List.length_ofFn];omega)]
  simp only [List.getElem_ofFn]
  congr 2;omega
namespace NetEmits
variable {α : Type} {ea : α→List Bool} {k w K : α→ℕ}
lemma firstProper {m : ∀x,BooleanNetwork (k x) (w x)} {f : ∀x,Fin (K x)→BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hm : NetEmits ea m)
    (hf : NetEmits (fun x:Σa,Fin (K a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetEmits ea (fun x=>BitArithmetic.firstProperNet (m x) (List.ofFn (f x))):=by
  let F:=fun x j=>BitArithmetic.firstProperNet (m x) ((List.ofFn (f x)).drop (K x-j))
  have h0 : NetEmits ea (fun x=>F x 0):=by
    have hz : NetEmits ea (fun x=>BitArithmetic.wordConstant (n:=k x) (0 : BitVec (w x))) := by
      simpa only [BitVec.ofNat_eq_ofNat] using wordConst hk hw (const _ _ 0)
    refine hz.congr ?_
    intro x
    dsimp only [F]
    rw [Nat.sub_zero,List.drop_eq_nil_of_le (by simp only [List.length_ofFn];exact le_rfl)]
    rfl
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
    have hd:=hf.compInput hy
    have hstep:=(properOn (hk.comp hx.fst) (hw.comp hx.fst) (hm.compInput hx.fst) hd).wordMux
      hd (ofCanonical hx.snd.snd) (hw.comp hx.fst)
    convert hstep using 1
    funext x
    dsimp only [F]
    rw [dropOfFn_step _ x.2.isLt,BitArithmetic.firstProperNet]
  have hb:=hk.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  have hw':=hw.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  have hc : NetworkAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length) (fun x=>F x.1 x.2.val):=by
    apply NetworkAt.firstProperNet (hm.countPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)) hw'
    · exact (hK.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)).of_le (by intro x;simp only [List.length_drop,List.length_ofFn];omega)
    · obtain ⟨p,hp⟩:=countPolyIndexed hK hf
      refine ⟨p,?_⟩
      intro x d hd
      obtain ⟨i,rfl⟩:=List.mem_ofFn.mp (List.mem_of_mem_drop hd)
      exact hp ⟨x.1,i⟩
  simpa only [F,Nat.sub_self,List.drop_zero] using boundedStages hK h0 hs hb hw' hc
end NetEmits
end ExactQuantumFactoring.NetworkEmission

end



end OAI
