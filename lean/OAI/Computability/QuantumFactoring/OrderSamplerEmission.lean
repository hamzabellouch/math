import Mathlib
import OAI.Computability.QuantumFactoring.NetworkModularPowerEmission
import OAI.Computability.QuantumFactoring.TriangularProgramEmission
import OAI.Computability.QuantumFactoring.PhysicalListEmission

namespace OAI



section
namespace ExactQuantumFactoring.OrderSamplerEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits CircuitEmission
variable {α : Type} {ea : α→List Bool} {w b s n : α→ℕ}
lemma inputWidth (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    Emits ea unaryCode (fun x=>OrderSample.inputWidth (w x) (b x)):=
  (hw.unaryAdd hw).unaryAdd (TriangularEmission.width hb)
lemma scratch (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    Emits ea unaryCode (fun x=>OrderSample.scratch (w x) (b x)):=
  hw.unaryAdd (hb.unaryMul (((((const _ _ 3672).unaryMul hw).unaryMul hw).unaryAdd
    ((const _ _ 436).unaryMul hw)).unaryAdd (const _ _ 36)))
lemma width (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    Emits ea unaryCode (fun x=>OrderSample.width (w x) (b x)):=
  ((inputWidth hw hb).unaryAdd hw).unaryAdd (scratch hw hb)
lemma powerInputs (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>OrderSample.powerInputs (w x) (b x)):=by
  apply selectSlice (inputWidth hw hb) ((hw.unaryAdd hw).unaryAdd hb) (const _ _ 0) _
  intro x i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [Fin.addCases_left,Fin.val_castAdd,Nat.zero_add]
  · simp only [Fin.addCases_right,Fin.val_natAdd,Nat.zero_add];rfl
lemma powerNetwork (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    NetEmits ea (fun x=>OrderSample.powerNetwork (w x) (b x)):=
  (powerInputs hw hb).comp (modularPower hw hb)
lemma initial (hw : Emits ea unaryCode w) (hb : Emits ea unaryCode b) :
    OpsEmits ea (fun x=>OrderSample.initial (w x) (b x)):=
  ((TriangularEmission.uniform hb).right (hw.unaryAdd hw)).first w (fun x=>OrderSample.scratch (w x) (b x))
lemma program (hw : Emits ea unaryCode w) (hs : Emits ea unaryCode s) :
    OpsEmits ea (fun x=>OrderSample.program (w x) (s x)):=by
  have hb:=hs.unaryAdd (const _ _ 2)
  exact (OpsEmits.oracleOn (powerNetwork hw hb) (fun x=>OrderSample.powerNetwork_count (w x) (s x+2))).append
    (((TriangularEmission.transform hs).right (hw.unaryAdd hw)).first w (fun x=>OrderSample.scratch (w x) (s x+2)))
lemma complete (hw : Emits ea unaryCode w) (hs : Emits ea unaryCode s) :
    OpsEmits ea (fun x=>OrderSample.completeSampler (w x) (s x)):=
  (initial hw (hs.unaryAdd (const _ _ 2))).append (program hw hs)
lemma guessWidth (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>OrderTrial.guessWidth (n x)):=
  hn.unaryAdd (hn.unaryAdd (hn.unaryAdd (retentionBits hn)))
lemma guessProgram (hn : Emits ea unaryCode n) : OpsEmits ea (fun x=>OrderTrial.guessProgram (n x)):=
  OpsEmits.parallel (OpsEmits.hadamards hn (fun _=>le_rfl))
    (OpsEmits.parallel (OpsEmits.hadamards hn (fun _=>le_rfl))
      (OpsEmits.parallel (OpsEmits.hadamards hn (fun _=>le_rfl))
        (OpsEmits.hadamards (retentionBits hn) (fun _=>le_rfl)) hn) hn) hn
lemma rawWidth (hw : Emits ea unaryCode w) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) :
    Emits ea unaryCode (fun x=>OrderTrial.rawWidth (w x) (s x) (n x)):=
  (const _ _ 2).unaryAdd ((width hw (hs.unaryAdd (const _ _ 2))).unaryAdd (guessWidth hn))
lemma rawProgram (hw : Emits ea unaryCode w) (hs : Emits ea unaryCode s) (hn : Emits ea unaryCode n) :
    OpsEmits ea (fun x=>OrderTrial.rawProgram (w x) (s x) (n x)):=
  OpsEmits.parallel (OpsEmits.hadamards (const _ _ 2) (fun _=>le_rfl))
    (OpsEmits.parallel (complete hw hs) (guessProgram hn) (width hw (hs.unaryAdd (const _ _ 2)))) (const _ _ 2)
end ExactQuantumFactoring.OrderSamplerEmission

end



end OAI
