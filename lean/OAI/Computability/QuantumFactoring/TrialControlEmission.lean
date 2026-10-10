import Mathlib
import OAI.Computability.QuantumFactoring.NetworkModularPowerEmission
import OAI.Computability.QuantumFactoring.RetentionEmission
import OAI.Computability.QuantumFactoring.EmissionDependentLists
import OAI.Computability.QuantumFactoring.PhysicalListEmission
import OAI.Computability.QuantumFactoring.RetentionTemplateEmission
import OAI.Computability.QuantumFactoring.GcdEmission

namespace OAI



section
namespace ExactQuantumFactoring.TrialControlEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits OrderTrial
variable {α : Type} {ea : α→List Bool} {k w n : α→ℕ}
def decodeEquiv : Fin 4 ≃ DecodeVar where
  toFun := ![.den,.num,.residue,.coin]
  invFun | .den=>0 | .num=>1 | .residue=>2 | .coin=>3
  left_inv i:=by fin_cases i <;> rfl
  right_inv i:=by cases i <;> rfl
lemma first {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hn : Emits ea unaryCode n)
    (hd : NetEmits ea d) (hj : NetEmits ea j) (ht : NetEmits ea t) (hc : NetEmits ea c) :
    NetEmits ea (fun x=>firstRetNet (n x) (d x) (j x) (t x) (c x)):=by
  apply retention decodeEquiv hk hw (BitStackProgram.Emits.retentionBits hn)
    (NetworkEmission.Emits.firstExpr hn (const _ _ (.var .den)) (const _ _ (.var .num))) (const _ _ (.var .coin))
  intro i;cases i
  · exact hd
  · exact hj
  · exact ht
  · exact hc
lemma second {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hn : Emits ea unaryCode n)
    (hd : NetEmits ea d) (hj : NetEmits ea j) (ht : NetEmits ea t) (hc : NetEmits ea c) :
    NetEmits ea (fun x=>secondRetNet (n x) (d x) (j x) (t x) (c x)):=by
  apply retention decodeEquiv hk hw (BitStackProgram.Emits.retentionBits hn)
    (NetworkEmission.Emits.secondExpr hn (const _ _ (.var .den)) (const _ _ (.var .num)) (const _ _ (.var .residue))) (const _ _ (.var .coin))
  intro i;cases i
  · exact hd
  · exact hj
  · exact ht
  · exact hc
lemma third {d j t c : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hn : Emits ea unaryCode n)
    (hd : NetEmits ea d) (hj : NetEmits ea j) (ht : NetEmits ea t) (hc : NetEmits ea c) :
    NetEmits ea (fun x=>thirdRetNet (n x) (d x) (j x) (t x) (c x)):=by
  apply retention decodeEquiv hk hw (BitStackProgram.Emits.retentionBits hn)
    (NetworkEmission.Emits.lastExpr hn (const _ _ (.var .den)) (const _ _ (.var .num))) (const _ _ (.var .coin))
  intro i;cases i
  · exact hd
  · exact hj
  · exact ht
  · exact hc
lemma reverse {e : ∀x,BooleanNetwork (k x) (w x)}
    (hw : Emits ea unaryCode w) (he : NetEmits ea e) :
    NetEmits ea (fun x=>(e x).rewire Fin.rev):=by
  apply he.rewire (fun _=>Fin.rev)
  apply ofFnDep 0 hw
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (w a)=>(x.2.val,x.1))
  exact (((hw.comp hx.snd).unaryNat.natSub (const _ _ 1)).natSub hx.fst.unaryNat).congr (by intro x; change w x.1 - 1 - x.2.val = w x.1 - (x.2.val+1); omega)
lemma powOn {a m e : ∀x,BooleanNetwork (k x) (w x)}
    (hw : Emits ea unaryCode w) (ha : NetEmits ea a) (hm : NetEmits ea m) (he : NetEmits ea e) :
    NetEmits ea (fun x=>BitArithmetic.powOn (a x) (m x) (e x)):=
  ((ha.pair hm).pair (reverse hw he)).comp (modularPower hw hw)
lemma labelValid {a m d j : ∀x,BooleanNetwork (k x) (w x)}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hd : NetEmits ea d) (hj : NetEmits ea j) :
    NetEmits ea (fun x=>labelValidNet (n x) (a x) (m x) (d x) (j x)):=
  ((wordConst hk hw (const _ _ 0)).wordLt hd hw).band
    ((hd.wordLt (wordConst hk hw (NetworkEmission.Emits.powTwo hn)) hw).band
      ((hj.wordLt hd hw).band
        ((((hj.pair hd).comp (gcd hw)).equalOn (wordConst hk hw (const _ _ 1)) hw).band
          ((powOn hw ha hm hd).equalOn (wordConst hk hw (const _ _ 1)) hw))))
lemma accept {a m mode d j t c : ∀x,BooleanNetwork (k x) (w x)} {selected : ∀x,BooleanNetwork (k x) 1}
    (hk : Emits ea unaryCode k) (hw : Emits ea unaryCode w) (hn : Emits ea unaryCode n)
    (ha : NetEmits ea a) (hm : NetEmits ea m) (hmode : NetEmits ea mode)
    (hd : NetEmits ea d) (hj : NetEmits ea j) (ht : NetEmits ea t) (hc : NetEmits ea c) (hs : NetEmits ea selected) :
    NetEmits ea (fun x=>trialAcceptOn (n x) (a x) (m x) (mode x) (d x) (j x) (t x) (c x) (selected x)):=
  (labelValid hk hw hn ha hm hd hj).band
    (((hmode.wordLt (wordConst hk hw (const _ _ 2)) hw).band (hs.band (first hk hw hn hd hj ht hc))).bor
      (((hmode.equalOn (wordConst hk hw (const _ _ 2)) hw).band
        ((ht.wordLt hd hw).band (second hk hw hn hd hj ht hc))).bor
          ((hmode.equalOn (wordConst hk hw (const _ _ 3)) hw).band (third hk hw hn hd hj ht hc))))
end ExactQuantumFactoring.TrialControlEmission

end



end OAI
