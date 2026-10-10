import Mathlib
import OAI.Computability.QuantumFactoring.FactorVerifierEmission

namespace OAI



section
namespace ExactQuantumFactoring.SortingEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {k w r : α→ℕ}
lemma paddedPair {a b : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hb : NetEmits ea b) :
    NetEmits ea (fun x=>BitArithmetic.paddedPair (a x) (b x)):=
  (zeroWord hk hw hb).bor ((zeroWord hk hw ha).bnot.band (ha.wordLe hb hw))
lemma head (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.headNet (w x) (r x)):=left hw (hw.tensorWidth hr)
lemma tail (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.tailNet (w x) (r x)):=right hw (hw.tensorWidth hr)
lemma keepHead {a : ∀x,BooleanNetwork (tensorWidth (w x) (r x)) (tensorWidth (w x) (r x))}
    (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) (ha : NetEmits ea a) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.keepHead (a x)):=
  (head hw hr).pair ((tail hw hr).comp ha)
lemma compareStep (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.compareStep (w x) (r x)):=by
  have ha:=head hw hr.unarySucc
  have hb:=(tail hw hr.unarySucc).comp (head hw hr)
  have hrest:=(tail hw hr.unarySucc).comp (tail hw hr)
  have hp:=paddedPair (hw.tensorWidth hr.unarySucc.unarySucc) hw ha hb
  exact (hp.wordMux ha hb hw).pair ((hp.wordMux hb ha hw).pair hrest)
lemma insert (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.insertNet (w x) (r x)):=by
  apply boundedStages hr (f:=fun x j=>BitArithmetic.SortedWords.insertNet (w x) j)
  · exact identity (hw.tensorWidth (const _ _ 1))
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (r a)=>(x.1,(x.2.val,erasePack (BitArithmetic.SortedWords.insertNet (w x.1) x.2.val))))
    exact (compareStep (hw.comp hx.fst) hx.snd.fst).comp
      (keepHead (hw.comp hx.fst) hx.snd.fst.unarySucc (ofCanonical hx.snd.snd))
  · exact ((hw.tensorWidth hr.unarySucc).unaryPoly.pull (fun x:Σa,Fin (r a+1)=>x.1)).of_le (by
      intro x;rw [tensorWidth_eq,tensorWidth_eq];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
  · exact ((hw.tensorWidth hr.unarySucc).unaryPoly.pull (fun x:Σa,Fin (r a+1)=>x.1)).of_le (by
      intro x;rw [tensorWidth_eq,tensorWidth_eq];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
  · have hb:=(hr.unaryPoly.mul (((PolyAt.const _ 498).mul hw.unaryPoly).add (PolyAt.const _ 114))).pull
      (fun x:Σa,Fin (r a+1)=>x.1)
    exact hb.of_le (by
      intro x
      exact (BitArithmetic.SortedWords.insertNet_count _ _).trans (Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega)))
lemma sort (hw : Emits ea unaryCode w) (hr : Emits ea unaryCode r) :
    NetEmits ea (fun x=>BitArithmetic.SortedWords.sortNet (w x) (r x)):=by
  apply boundedStages hr (f:=fun x j=>BitArithmetic.SortedWords.sortNet (w x) j)
  · exact identity (const _ _ 0)
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (r a)=>(x.1,(x.2.val,erasePack (BitArithmetic.SortedWords.sortNet (w x.1) x.2.val))))
    exact (keepHead (hw.comp hx.fst) hx.snd.fst (ofCanonical hx.snd.snd)).comp (insert (hw.comp hx.fst) hx.snd.fst)
  · exact ((hw.tensorWidth hr).unaryPoly.pull (fun x:Σa,Fin (r a+1)=>x.1)).of_le (by
      intro x;rw [tensorWidth_eq,tensorWidth_eq];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
  · exact ((hw.tensorWidth hr).unaryPoly.pull (fun x:Σa,Fin (r a+1)=>x.1)).of_le (by
      intro x;rw [tensorWidth_eq,tensorWidth_eq];exact Nat.mul_le_mul_right _ (by have:=x.2.isLt;omega))
  · have hb:=((hr.unaryPoly.mul hr.unaryPoly).mul (((PolyAt.const _ 498).mul hw.unaryPoly).add (PolyAt.const _ 114))).pull
      (fun x:Σa,Fin (r a+1)=>x.1)
    exact hb.of_le (by
      intro x
      exact (BitArithmetic.SortedWords.sortNet_count _ _).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul (by have:=x.2.isLt;omega) (by have:=x.2.isLt;omega))))
end ExactQuantumFactoring.SortingEmission

end



end OAI
