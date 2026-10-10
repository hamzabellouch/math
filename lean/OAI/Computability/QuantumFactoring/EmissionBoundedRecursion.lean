import Mathlib
import OAI.Computability.QuantumFactoring.WordBlocksEmission

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Emits
open Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool}

def recursionCode (K : α→ℕ) (f : α→ℕ→β) (x : Σa,Fin (K a+1)) : List Bool:=
  prodCode ea (prodCode unaryCode eb) (x.1,(x.2.val,f x.1 x.2.val))
def recursionNext (K : α→ℕ) (x : Σa,Fin (K a+1)) : Σa,Fin (K a+1):=
  ⟨x.1,⟨min (x.2.val+1) (K x.1),by omega⟩⟩
lemma recursionNext_iterate (K : α→ℕ) (x : Σa,Fin (K a+1)) (j : ℕ) :
    ((recursionNext K)^[j]) x=⟨x.1,⟨min (x.2.val+j) (K x.1),by omega⟩⟩:=by
  rcases x with ⟨a,i⟩
  induction j with
  | zero=>
    change (⟨a,i⟩ : Σa,Fin (K a+1))=⟨a,_⟩
    apply congrArg (fun i:Fin (K a+1)=>(⟨a,i⟩ : Σa,Fin (K a+1)))
    apply Fin.ext
    dsimp only
    have := i.isLt
    omega
  | succ j ih=>
    rw [Function.iterate_succ_apply',ih]
    dsimp only [recursionNext]
    apply congrArg (fun i:Fin (K a+1)=>(⟨a,i⟩ : Σa,Fin (K a+1)))
    apply Fin.ext
    dsimp only
    omega
/-- A charged finite-stack loop over an explicitly implemented next-stage
construction. The size invariant is a bound on actual intermediate encodings,
not an assumption that an arbitrary bounded function is computable. -/
lemma boundedRecursion (K : α→ℕ) (f : α→ℕ→β)
    (hK : Emits ea unaryCode K) (h0 : Emits ea eb (fun x=>f x 0))
    (hs : Emits (recursionCode (ea:=ea) (eb:=eb) K f) eb
      (fun x=>f x.1 (min (x.2.val+1) (K x.1))))
    (hb : PolyAt (fun x:Σa,Fin (K a+1)=>(ea x.1).length)
      (fun x=>(eb (f x.1 x.2.val)).length)) :
    Emits ea eb (fun x=>f x (K x)):=by
  let ec:=recursionCode (ea:=ea) (eb:=eb) K f
  have hx : Emits ec (prodCode ea (prodCode unaryCode eb))
      (fun x=>(x.1,(x.2.val,f x.1 x.2.val))):=
    (id (prodCode ea (prodCode unaryCode eb))).precompose _
  have hcount:=hx.snd.fst
  have hk:=hK.comp hx.fst
  have hi : Emits ec unaryCode (fun x=>min (x.2.val+1) (K x.1)):=
    ((ofProcedure clippedUnary).comp (hk.pair hcount.unarySucc.unaryNat)).congr (by intro x;exact Nat.min_comm _ _)
  have hn : Emits ec ec (recursionNext K):=
    (hx.fst.pair (hi.pair hs)).result (by intro x;rfl)
  obtain ⟨pn⟩:=hn
  obtain ⟨pk⟩:=hK
  obtain ⟨P,hP⟩:=hb
  let Q : Polynomial ℕ:=Polynomial.C 4*Polynomial.X+Polynomial.C 2*pk.bound+P+Polynomial.C 4
  have bound : ∀x:Σa,Fin (K a+1),(ec x).length≤Q.eval (ea x.1).length:=by
    intro x
    have ha:=pk.output_length_le x.1
    have hv:=hP x
    dsimp only at hv
    have hi:=x.2.isLt
    simp only [unaryCode,List.length_replicate] at ha
    simp only [ec,recursionCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
    simp only [Q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega
  let pi:=pn.iterate Q (by
    intro j x i hi
    rw [recursionNext_iterate]
    apply (bound _).trans
    apply eval_nat_mono
    simp only [ec,recursionCode,prodCode,pairBits_length,unaryCode,List.length_replicate]
    omega)
  have hz : Emits ea ec (fun x=>(⟨x,⟨0,by omega⟩⟩ : Σa,Fin (K a+1))):=
    ((id ea).pair ((const ea unaryCode 0).pair h0)).result (by intro x;rfl)
  have hout:=hx.snd.snd.comp ((ofProcedure pi).comp ((ofProcedure pk).pair hz))
  exact hout.congr (by intro x;dsimp only;rw [recursionNext_iterate];simp only [Nat.zero_add,min_self])
end ExactQuantumFactoring.BitStackProgram.Emits

end



end OAI
