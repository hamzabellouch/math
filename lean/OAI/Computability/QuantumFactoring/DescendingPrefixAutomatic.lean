import Mathlib
import OAI.Computability.QuantumFactoring.DescendingStepEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Emits
lemma filterPrefixEmits {α : Type} {ea : α→List Bool} {k S W : α→ℕ} {w : α→ℕ→ℕ}
    (prev : ∀x s,BooleanNetwork (w x (s+1)) (w x s))
    (keep : ∀x s,BooleanNetwork (k x) (w x (s+1))→BooleanNetwork (k x) 1)
    (hp : ∀x s,(prev x s).net.count=0)
    (hw : ∀x s,s≤S x→w x s≤W x)
    (v : ∀x,BooleanNetwork (k x) (w x (S x)))
    (hS : Emits ea unaryCode S) (hk : Emits ea unaryCode k) (hV : NetEmits ea v)
    (hW : PolyAt (fun x=>(ea x).length) W)
    (hep : NetEmits (prodCode ea unaryCode) (fun x=>prev x.1 x.2))
    (hec : NetEmits (fun x:Σa,Σs,BooleanNetwork (k a) (w a (s+1))=>
      prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.1,erasePack x.2.2))) (fun x=>keep x.1 x.2.1 x.2.2)) :
    NetEmits ea (fun x=>filterPrefix (prev x) (keep x) (S x) (v x)):=by
  let ix:=Σa,Σs:Fin (S a),{r:BooleanNetwork (k a) (w a (s.val+1)) // r.net.count≤(v a).net.count}
  let enc:ix→List Bool:=fun x=>prodCode ea (prodCode unaryCode packCode) (x.1,(x.2.1.val,erasePack x.2.2.val))
  have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
    (fun x:ix=>(x.1,(x.2.1.val,erasePack x.2.2.val)))
  let g:ix→Σa,Σs,BooleanNetwork (k a) (w a (s+1)):=fun x=>⟨x.1,x.2.1.val,x.2.2.val⟩
  have he:=hec.compInput (hx.recode (g:=g) (fun _=>rfl))
  have hb : PolyAt (fun x:ix=>(ea x.1).length) (fun x=>(enc x).length):=by
    have hbound:=(PolyAt.const _ 104).mul ((((hk.unaryPoly.add hV.countPoly).add hW).add (PolyAt.const _ 1)).pow 2)
    apply ((((PolyAt.const _ 2).mul (PolyAt.self _)).add
      (((PolyAt.const _ 2).mul hS.unaryPoly).add hbound)).add (PolyAt.const _ 2)).pull (fun x:ix=>x.1) |>.of_le
    intro x
    have hs:=x.2.1.isLt
    have hc:=x.2.2.property
    have hw':=hw x.1 (x.2.1.val+1) (by omega)
    have hp':=(packCode_bound (erasePack x.2.2.val)).trans
      (Nat.mul_le_mul_left 104 (Nat.pow_le_pow_left (show k x.1+x.2.2.val.net.count+w x.1 (x.2.1.val+1)+1≤
        k x.1+(v x.1).net.count+W x.1+1 by omega) 2))
    simp only [enc,prodCode,pairBits_length,unaryCode,List.length_replicate]
    omega
  obtain ⟨p,hp'⟩:=he.countPoly.rebase hb
  exact filterPrefixEmitter (C:=fun x=>p.eval (ea x).length) prev keep hp
    (fun x s hs r hr=>hp' ⟨x,⟨s,hs⟩,r,hr⟩) hw v (fun _=>le_rfl) hS hk hV
    hV.countPoly ⟨p,fun _=>le_rfl⟩ hW (filterStepEmitter prev keep hep hec)
end ExactQuantumFactoring.NetworkEmission

end



end OAI
