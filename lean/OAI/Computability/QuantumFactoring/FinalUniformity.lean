import Mathlib
import OAI.Computability.QuantumFactoring.RetainedTreeEmission
import OAI.Computability.QuantumFactoring.QuarterRetentionEmission

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
lemma paddedFlag (hn : Emits ea unaryCode n) (hn0 : ∀x,0<n x) :
    NetEmits ea (fun x=>PhysicalTree.paddedFlag (n x) (hn0 x)):=
  ((paddedHistory hn).comp (accepted hn (steps hn) hn0)).band ((paddedPad hn).comp (padFlag hn))
lemma quarterFlag (hn : Emits ea unaryCode n) (hn0 : ∀x,0<n x) :
    NetEmits ea (fun x=>PhysicalTree.quarterFlag (n x) (hn0 x)):=
  ((quarterRare hn).bnot.band (((quarterOrd hn).comp (paddedFlag hn hn0)).band (quarterOrdKeep hn))).bor
    ((quarterRare hn).band ((quarterGuessFlag hn).band (quarterGuessKeep hn)))
end ExactQuantumFactoring.PhysicalTreeEmission
namespace ExactQuantumFactoring.PhysicalTree
open BitStackProgram BitStackProgram.Emits
/-- A single finite Boolean-stack TM2 generates the literal family in polynomial
unary-input time, including all compile-time expression and primality decisions. -/
theorem finalCircuit_uniform : Uniform finalCircuit:=by
  have hn : Emits unaryCode unaryCode paddedLength:=
    (const unaryCode unaryCode 128).unaryMax (BitStackProgram.Emits.id unaryCode)
  exact UniformResources.PhysicalTree.uniform_of_quarter_emitters_clean
    (PhysicalTreeEmission.quarterWidth hn) (PhysicalTreeEmission.quarterProgram hn)
    (PhysicalTreeEmission.quarterFlag hn paddedLength_pos) (PhysicalTreeEmission.quarterOutput hn)
end ExactQuantumFactoring.PhysicalTree

end



end OAI
