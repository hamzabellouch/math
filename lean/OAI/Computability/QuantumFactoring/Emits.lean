import Mathlib
import OAI.Computability.QuantumFactoring.EmissionCombinators
import OAI.Computability.QuantumFactoring.BitStackBoundedPrime

namespace OAI

section
namespace ExactQuantumFactoring.BitStackProgram

namespace Emits
open Procedure
variable {α : Type} {ea : α→List Bool}
lemma natLt {f g : α→ℕ} (hf : Emits ea Nat.bits f) (hg : Emits ea Nat.bits g) :
    Emits ea boolCode (fun x=>decide (f x<g x)):=(ofProcedure binaryLt).comp (hf.pair hg)
lemma natEq {f g : α→ℕ} (hf : Emits ea Nat.bits f) (hg : Emits ea Nat.bits g) :
    Emits ea boolCode (fun x=>decide (f x=g x)):=(ofProcedure binaryEq).comp (hf.pair hg)
lemma boolNot {f : α→Bool} (hf : Emits ea boolCode f) : Emits ea boolCode (fun x=>!f x):=
  (ofProcedure Procedure.boolNot).comp hf
lemma boolAnd {f g : α→Bool} (hf : Emits ea boolCode f) (hg : Emits ea boolCode g) :
    Emits ea boolCode (fun x=>f x&&g x):=(ofProcedure Procedure.boolAnd).comp (hf.pair hg)
lemma boolOr {f g : α→Bool} (hf : Emits ea boolCode f) (hg : Emits ea boolCode g) :
    Emits ea boolCode (fun x=>f x||g x):=(ofProcedure Procedure.boolOr).comp (hf.pair hg)
lemma unaryPrime {f : α→ℕ} (hf : Emits ea unaryCode f) : Emits ea boolCode (fun x=>decide (Nat.Prime (f x))):=
  (ofProcedure Procedure.unaryPrime).comp hf
end Emits
end ExactQuantumFactoring.BitStackProgram

end



end OAI
