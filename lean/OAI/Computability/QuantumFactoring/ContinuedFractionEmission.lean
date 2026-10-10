import Mathlib
import OAI.Computability.QuantumFactoring.EmissionLengthBounds
import OAI.Computability.QuantumFactoring.NetworkAtArithmetic
import OAI.Computability.QuantumFactoring.NetworkRecursionEmission
import OAI.Computability.QuantumFactoring.RootCircuitEmission

namespace OAI



section
namespace ExactQuantumFactoring.NetworkEmission.NetEmits
open BitStackProgram BitStackProgram.Emits BitArithmetic
variable {α : Type} {ea : α→List Bool} {w K : α→ℕ}
lemma div (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.div (w x)):=
  ⟨fun x=>AIGNetworkEmission.binaryPack NativeAIG.divide (w x),
    (ofProcedure AIGNetworkEmission.Emission.divPackP).comp hw,fun x=>AIGNetworkEmission.divPack_value (w x)⟩
lemma cfHead (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.cfHead (w x)):=
  selectSlice (hw.unaryAdd (hw.unaryAdd hw)) hw (const _ _ 0) _ (by intros;simp only [Fin.val_castAdd,Nat.zero_add])
lemma cfTail (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.cfTail (w x)):=
  selectSlice (hw.unaryAdd (hw.unaryAdd hw)) (hw.unaryAdd hw) hw.unaryNat _ (by intros;rfl)
lemma cfP (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.cfP (w x)):=
  (cfTail hw).comp (rootModulus hw)
lemma cfQ (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.cfQ (w x)):=
  (cfTail hw).comp (rootGuess hw)
lemma cfProduct (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.cfProduct (w x)):=
  ((((cfHead hw).pair (cfP hw)).comp (mul hw)).pair (cfQ hw)).comp (add hw)
lemma cfCombine (hw : Emits ea unaryCode w) : NetEmits ea (fun x=>BitArithmetic.cfCombine (w x)):=by
  have hd:=cfP hw
  have hc:=hd.equalOn (wordConst (hw.unaryAdd (hw.unaryAdd hw)) hw (const _ _ 0)) hw
  exact (hc.wordMux (cfHead hw) (cfProduct hw) hw).pair
    (hc.wordMux (wordConst (hw.unaryAdd (hw.unaryAdd hw)) hw (const _ _ 1)) hd hw)
lemma convergent (hw : Emits ea unaryCode w) (hK : Emits ea unaryCode K) :
    NetEmits ea (fun x=>BitArithmetic.convergentNet (w x) (K x)):=by
  apply boundedStages hK (f:=fun x j=>BitArithmetic.convergentNet (w x) j)
  · exact (div hw).pair (wordConst (hw.unaryAdd hw) hw (const _ _ 1))
  · have hx:=(BitStackProgram.Emits.id (prodCode ea (prodCode unaryCode packCode))).precompose
      (fun x:Σa,Fin (K a)=>(x.1,(x.2.val,erasePack (BitArithmetic.convergentNet (w x.1) x.2.val))))
    have h:=hw.comp hx.fst
    exact (((div h).pair ((rootGuess h).pair (mod h))).comp
      ((cfHead h).pair ((cfTail h).comp (ofCanonical hx.snd.snd)))).comp (cfCombine h)
  · exact (hw.unaryPoly.add hw.unaryPoly).pull (fun x:Σa,Fin (K a+1)=>x.1)
  · exact (hw.unaryPoly.add hw.unaryPoly).pull (fun x:Σa,Fin (K a+1)=>x.1)
  · exact NetworkAt.convergentNet (hw.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1))
      ((hK.unaryPoly.pull (fun x:Σa,Fin (K a+1)=>x.1)).of_le (by intro x;have:=x.2.isLt;omega))
end ExactQuantumFactoring.NetworkEmission.NetEmits

end


end OAI
