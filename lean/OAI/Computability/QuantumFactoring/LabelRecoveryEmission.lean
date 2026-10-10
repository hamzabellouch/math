import Mathlib
import OAI.Computability.QuantumFactoring.RecoveryPolynomial
import OAI.Computability.QuantumFactoring.ContinuedFractionEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits BitArithmetic OrderTrial
variable {α : Type} {ea : α→List Bool} {n w K : α→ℕ}
lemma checkedConvergent {Q B k : ∀x,BooleanNetwork (n x) (w x)}
    (hn : Emits ea unaryCode n) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hQ : NetEmits ea Q) (hB : NetEmits ea B) (hk : NetEmits ea k) :
    NetEmits ea (fun x=>OrderTrial.checkedConvergent (K x) (Q x) (B x) (k x)):=by
  have hc:=(hk.pair hQ).comp (convergent hw hK)
  have hd:=hc.comp (rootGuess hw)
  have hj:=hc.comp (rootModulus hw)
  have hp : NetEmits ea (fun x=>binCheckExpr.isOne ![Q x,B x,k x,
      ((k x).pair (Q x) |>.comp (convergentNet (w x) (K x))).comp (BitArithmetic.rootGuess (w x)),
      ((k x).pair (Q x) |>.comp (convergentNet (w x) (K x))).comp (BitArithmetic.rootModulus (w x))]):=by
    apply isOne (const _ _ binCheckExpr) hn hw
    intro i;fin_cases i
    · exact hQ
    · exact hB
    · exact hk
    · exact hd
    · exact hj
  exact (hp.wordMux hd (wordConst hn hw (const _ _ 0)) hw).pair
    (hp.wordMux hj (wordConst hn hw (const _ _ 0)) hw)
lemma pairChoice (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>OrderTrial.pairChoice (w x)):=by
  have hw2:=hw.unaryAdd hw
  have hl:=rootModulus hw2
  have hr:=rootGuess hw2
  exact ((hl.comp (rootModulus hw)).equalOn (wordConst (hw2.unaryAdd hw2) hw (const _ _ 0)) hw).wordMux hr hl hw2
lemma recovery {Q B k : ∀x,BooleanNetwork (n x) (w x)}
    (hn : Emits ea unaryCode n) (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K)
    (hQ : NetEmits ea Q) (hB : NetEmits ea B) (hk : NetEmits ea k) :
    NetEmits ea (fun x=>OrderTrial.recoveryNet (Q x) (B x) (k x) (K x)):=by
  apply boundedStages hK (f:=fun x j=>OrderTrial.recoveryNet (Q x) (B x) (k x) j)
  · exact (wordConst hn hw (const _ _ 0)).pair (wordConst hn hw (const _ _ 0))
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (K a)=>(x.1,(x.2.val,erasePack (OrderTrial.recoveryNet (Q x.1) (B x.1) (k x.1) x.2.val))))
    exact ((checkedConvergent (hn.comp hx.fst) (hw.comp hx.fst) hx.snd.fst
      (hQ.compInput hx.fst) (hB.compInput hx.fst) (hk.compInput hx.fst)).pair
        (ofCanonical hx.snd.snd)).comp (pairChoice (hw.comp hx.fst))
  · exact hn.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)
  · exact (hw.unaryPoly.add hw.unaryPoly).pull (fun x:Σa,Fin (K a+1)=>x.1)
  · exact OrderTrial.recoveryNet_poly
      (hQ.count.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1))
      (hB.count.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1))
      (hk.count.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1))
      (hw.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1))
      ((hK.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)).of_le (by intro x;have:=x.2.isLt;omega))
end ExactQuantumFactoring.NetworkEmission.NetEmits

end



end OAI
