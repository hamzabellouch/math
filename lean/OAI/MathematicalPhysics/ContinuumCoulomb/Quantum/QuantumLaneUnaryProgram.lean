import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialSlotProgram
import OAI.Computability.QuantumFactoring.BitStackBoundedUnary

namespace OAI

/-! Lane colors can be produced in unary without expanding the binary cell
coordinates: only their residues modulo three enter the lane formula. -/

noncomputable section
namespace ContinuumCoulomb.QuantumLaneUnaryProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode QuantumOrdinalProgram

private noncomputable def residue {α : Type} {ea : α → List Bool} {f : α → ℕ}
    (p : Procedure ea Nat.bits f) : Procedure ea unaryCode (fun x => f x%3) :=
  Procedure.boundedUnary
    (Procedure.binaryMod.comp (p.pair (Procedure.constant ea Nat.bits 3)))
    (Procedure.constant ea unaryCode 3)
    (by intro x; exact (Nat.mod_lt (f x) (by decide)).le)

noncomputable def program (B : ℕ) :
    Procedure inputCode unaryCode (QuantumSpatialSlotProgram.lane B) := by
  let p := QuantumSpatialSlotProgram.cellProgram
  let row := residue ((Procedure.first Nat.bits Nat.bits).comp p)
  let col := residue ((Procedure.second Nat.bits Nat.bits).comp p)
  let rowTerm := Procedure.unaryMul.comp ((Procedure.constant inputCode unaryCode (3*B)).pair row)
  let colTerm := Procedure.unaryMul.comp ((Procedure.constant inputCode unaryCode B).pair col)
  exact Procedure.unaryAdd.comp
    ((Procedure.unaryAdd.comp (QuantumOrdinalProgram.program.pair colTerm)).pair rowTerm)

end ContinuumCoulomb.QuantumLaneUnaryProgram

end

end OAI
