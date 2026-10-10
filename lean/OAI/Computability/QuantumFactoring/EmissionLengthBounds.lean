import Mathlib
import OAI.Computability.QuantumFactoring.NetworkAt
import OAI.Computability.QuantumFactoring.NetworkModularEmission
import OAI.Computability.QuantumFactoring.NetworkSequenceEmission

namespace OAI



section

namespace ExactQuantumFactoring.PolyAt
variable {α : Sort*} {l k f : α→ℕ}
lemma rebase (hf : PolyAt k f) (hk : PolyAt l k) : PolyAt l f:=by
  obtain ⟨p,hp⟩:=hf
  obtain ⟨q,hq⟩:=hk
  exact ⟨p.comp q,fun x=>by
    simpa only [Polynomial.eval_comp] using (hp x).trans (PolyBound.eval_mono p (hq x))⟩
end ExactQuantumFactoring.PolyAt

namespace ExactQuantumFactoring.BitStackProgram.Emits
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}
lemma lengthPoly {f : α→β} (hf : Emits ea eb f) :
    PolyAt (fun x=>(ea x).length) (fun x=>(eb (f x)).length):=by
  obtain ⟨p⟩:=hf
  exact ⟨Polynomial.X+p.bound,fun x=>by simpa using p.output_length_le x⟩
lemma unaryPoly {f : α→ℕ} (hf : Emits ea unaryCode f) :
    PolyAt (fun x=>(ea x).length) f:=by
  simpa only [unaryCode,List.length_replicate] using hf.lengthPoly
lemma indexCode_poly {k : α→ℕ} (hk : Emits ea unaryCode k) :
    PolyAt (fun x:Σa,Fin (k a)=>(ea x.1).length)
      (fun x=> (prodCode unaryCode ea (x.2.val,x.1)).length):=by
  have hb:=hk.unaryPoly.pull (fun x:Σa,Fin (k a)=>x.1)
  exact (((PolyAt.const _ 2).mul hb).add (PolyAt.self _)).add (PolyAt.const _ 2) |>.of_le (by
    intro x
    simp only [prodCode,pairBits_length,unaryCode,List.length_replicate]
    have := x.2.isLt
    omega)
end ExactQuantumFactoring.BitStackProgram.Emits

namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits
variable {α : Type} {ea : α→List Bool} {n m k : α→ℕ}
lemma countPoly {f : ∀x,BooleanNetwork (n x) (m x)} (hf : NetEmits ea f) :
    NetworkAt (fun x=>(ea x).length) f:=hf.count.unaryPoly
lemma countPolyIndexed {f : ∀x,Fin (k x)→BooleanNetwork (n x) (m x)}
    (hk : Emits ea unaryCode k)
    (hf : NetEmits (fun x:Σa,Fin (k a)=>prodCode unaryCode ea (x.2.val,x.1)) (fun x=>f x.1 x.2)) :
    NetworkAt (fun x:Σa,Fin (k a)=>(ea x.1).length) (fun x=>f x.1 x.2):=
  hf.countPoly.rebase hk.indexCode_poly
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI
