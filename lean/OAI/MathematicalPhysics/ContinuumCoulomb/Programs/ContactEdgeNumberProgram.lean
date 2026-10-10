import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactEdgeNumber
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ContactPlacedGadgetProgram

namespace OAI

/-! Each fixed local edge has an explicit polynomial-time global lookup
index, with the original source edge index retained. -/

namespace ContinuumCoulomb.ContactEdgeNumberProgram
open ExactQuantumFactoring.BitStackProgram ContactMediator

abbrev Input := ℕ × ℕ

def inputCode : Input → List Bool := prodCode unaryCode unaryCode

noncomputable opaque rProgram : Procedure inputCode Nat.bits Prod.fst :=
  Procedure.unaryToBits.comp (Procedure.first unaryCode unaryCode)

noncomputable opaque eProgram : Procedure inputCode Nat.bits Prod.snd :=
  Procedure.unaryToBits.comp (Procedure.second unaryCode unaryCode)

noncomputable opaque twiceRProgram : Procedure inputCode Nat.bits (fun x => x.1 * 2) :=
  Procedure.binaryMul.comp (rProgram.pair (Procedure.constant inputCode Nat.bits 2))

noncomputable opaque twiceEProgram : Procedure inputCode Nat.bits (fun x => x.2 * 2) :=
  Procedure.binaryMul.comp (eProgram.pair (Procedure.constant inputCode Nat.bits 2))

noncomputable def pathProgram : (p : LocalPath) →
    Procedure inputCode Nat.bits (fun x => pathNumber x.1 x.2 p)
  | Sum.inl s => Procedure.binaryAdd.comp
      (twiceEProgram.pair (Procedure.constant inputCode Nat.bits s.val))
  | Sum.inr (s, t) =>
      let a := Procedure.binaryAdd.comp
        (twiceEProgram.pair (Procedure.constant inputCode Nat.bits s.val))
      let b := Procedure.binaryMul.comp (a.pair (Procedure.constant inputCode Nat.bits 2))
      let c := Procedure.binaryAdd.comp (twiceRProgram.pair b)
      Procedure.binaryAdd.comp (c.pair (Procedure.constant inputCode Nat.bits t.val))

noncomputable opaque pathCountProgram : Procedure inputCode Nat.bits
    (fun x => x.1 * 2 + x.1 * 2 * 2) :=
  Procedure.binaryAdd.comp (twiceRProgram.pair
    (Procedure.binaryMul.comp (twiceRProgram.pair (Procedure.constant inputCode Nat.bits 2))))

noncomputable def edgeProgram : (a : LocalEdge) →
    Procedure inputCode Nat.bits (fun x => edgeNumber x.1 x.2 a)
  | Sum.inl _ => eProgram
  | Sum.inr (Sum.inl p) => Procedure.binaryAdd.comp (rProgram.pair (pathProgram p))
  | Sum.inr (Sum.inr (p, t)) =>
      let base := Procedure.binaryAdd.comp (rProgram.pair pathCountProgram)
      let twice := Procedure.binaryMul.comp
        ((pathProgram p).pair (Procedure.constant inputCode Nat.bits 2))
      let b := Procedure.binaryAdd.comp (base.pair twice)
      Procedure.binaryAdd.comp (b.pair (Procedure.constant inputCode Nat.bits t.val))

noncomputable def certificate (a : LocalEdge) : Turing.TM2ComputableInPolyTime inputCode
    Nat.bits (fun x => edgeNumber x.1 x.2 a) := (edgeProgram a).toTM2

end ContinuumCoulomb.ContactEdgeNumberProgram

end OAI
