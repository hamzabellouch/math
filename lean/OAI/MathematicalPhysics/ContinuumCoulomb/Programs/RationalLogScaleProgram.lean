import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalLogScale
import OAI.Computability.QuantumFactoring.BitStackPowers

namespace OAI

/-! The logarithmic scale is computed from a binary power and a literal
bit-counting machine. Its fixed rational multiplier is independent of the
input instance. -/

namespace ContinuumCoulomb.RationalLogScale
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque powerProgram (k : ℕ) : Procedure unaryCode Nat.bits
    (fun N => N ^ k) :=
  Procedure.binaryPow.comp
    ((Procedure.constant unaryCode unaryCode k).pair Procedure.unaryToBits)

noncomputable opaque bitLengthProgram (k : ℕ) : Procedure unaryCode unaryCode
    (fun N => (N ^ k).bits.length) :=
  (Procedure.length.precompose Nat.bits).comp (powerProgram k)

noncomputable opaque bitLengthRationalProgram (k : ℕ) : Procedure unaryCode ratCode
    (fun N => ((N ^ k).bits.length : ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp (bitLengthProgram k))

noncomputable opaque program (c : ℚ) (k : ℕ) : Procedure unaryCode ratCode (value c k) :=
  Procedure.ratMul.comp
    ((Procedure.constant unaryCode ratCode c).pair (bitLengthRationalProgram k))

noncomputable def certificate (c : ℚ) (k : ℕ) :
    Turing.TM2ComputableInPolyTime unaryCode ratCode (value c k) :=
  (program c k).toTM2

end ContinuumCoulomb.RationalLogScale

end OAI
