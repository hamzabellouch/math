import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedDetour
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteProgram

namespace OAI

/-! Literal binary TM2 programs for every buffered endpoint path point. -/

noncomputable section
namespace ContinuumCoulomb.QuantumBufferedCode
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

noncomputable opaque uProgram : Procedure axisCode Nat.bits (fun x => x.1.1) := axisStartProgram
noncomputable opaque vProgram : Procedure axisCode Nat.bits (fun x => x.1.2) := axisEndProgram
noncomputable opaque kProgram : Procedure axisCode Nat.bits (fun x => x.2) := axisCursorProgram
noncomputable def constProgram (k : ℕ) : Procedure axisCode Nat.bits (fun _ => k) :=
  Procedure.constant axisCode Nat.bits k

noncomputable opaque horizontalProgram : Procedure axisCode Nat.bits (fun x => x.1.2-17) :=
  Procedure.binarySub.comp (vProgram.pair (constProgram 17))
noncomputable opaque verticalProgram : Procedure axisCode Nat.bits (fun x => x.1.1-17) :=
  Procedure.binarySub.comp (uProgram.pair (constProgram 17))
noncomputable opaque doglegCutProgram : Procedure axisCode Nat.bits (fun x => (x.1.2-17)+(x.1.1-17)) :=
  Procedure.binaryAdd.comp (horizontalProgram.pair verticalProgram)

noncomputable opaque doglegProgram : Procedure axisCode pairCode
    (fun x => qmaBufferedDoglegPoint x.1.1 x.1.2 x.2) := by
  let first := (Procedure.binaryAdd.comp ((constProgram 17).pair kProgram)).pair (constProgram 17)
  let second := vProgram.pair (Procedure.binaryAdd.comp ((constProgram 17).pair
    (Procedure.binarySub.comp (kProgram.pair horizontalProgram))))
  let last := uProgram.pair uProgram
  exact (Procedure.conditional (Procedure.binaryLe.comp (kProgram.pair horizontalProgram)) first
    (Procedure.conditional (Procedure.binaryLe.comp (kProgram.pair doglegCutProgram)) second last)).congrFun
      (by intro x; simp [qmaBufferedDoglegPoint])

noncomputable opaque totalProgram : Procedure axisCode Nat.bits (fun x => x.1.1+x.1.2) :=
  Procedure.binaryAdd.comp (uProgram.pair vProgram)
noncomputable opaque detourCutProgram : Procedure axisCode Nat.bits (fun x => x.1.1+x.1.2-9) :=
  Procedure.binarySub.comp (totalProgram.pair (constProgram 9))
noncomputable opaque twiceUProgram : Procedure axisCode Nat.bits (fun x => 2*x.1.1) :=
  Procedure.binaryMul.comp ((constProgram 2).pair uProgram)

noncomputable opaque detourProgram : Procedure axisCode pairCode
    (fun x => qmaBufferedDetourPoint x.1.1 x.1.2 x.2) := by
  let first := (Procedure.binarySub.comp ((constProgram 17).pair kProgram)).pair (constProgram 17)
  let second := (constProgram 9).pair (Procedure.binaryAdd.comp (kProgram.pair (constProgram 9)))
  let third := (Procedure.binaryAdd.comp ((Procedure.binarySub.comp (kProgram.pair uProgram)).pair
    (constProgram 9))).pair (Procedure.binaryAdd.comp (uProgram.pair (constProgram 9)))
  let fourth := vProgram.pair (Procedure.binarySub.comp
    ((Procedure.binaryAdd.comp (twiceUProgram.pair vProgram)).pair kProgram))
  let last := uProgram.pair uProgram
  exact (Procedure.conditional (Procedure.binaryLe.comp (kProgram.pair (constProgram 8))) first
    (Procedure.conditional (Procedure.binaryLe.comp (kProgram.pair uProgram)) second
      (Procedure.conditional (Procedure.binaryLe.comp (kProgram.pair detourCutProgram)) third
        (Procedure.conditional (Procedure.binaryLe.comp (kProgram.pair totalProgram)) fourth last)))).congrFun
          (by intro x; simp [qmaBufferedDetourPoint])

noncomputable def doglegCertificate : Turing.TM2ComputableInPolyTime axisCode pairCode
    (fun x => qmaBufferedDoglegPoint x.1.1 x.1.2 x.2) := doglegProgram.toTM2
noncomputable def detourCertificate : Turing.TM2ComputableInPolyTime axisCode pairCode
    (fun x => qmaBufferedDetourPoint x.1.1 x.1.2 x.2) := detourProgram.toTM2

end ContinuumCoulomb.QuantumBufferedCode

end

end OAI
