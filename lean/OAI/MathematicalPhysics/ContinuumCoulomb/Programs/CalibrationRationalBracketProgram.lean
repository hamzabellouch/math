import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RationalLogScaleProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibrationRationalBracket

namespace OAI

/-! A literal polynomial-time program returns both rational contact-search
endpoints from the unary instance-size parameter. -/

namespace ContinuumCoulomb.CalibrationRationalBracket
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque leftProgram (ε c : ℚ) (k : ℕ) : Procedure unaryCode ratCode
    (fun N => (endpoints ε (RationalLogScale.value c k N)).1) :=
  Procedure.ratMul.comp
    ((Procedure.constant unaryCode ratCode (1 - ε / 2)).pair (RationalLogScale.program c k))

noncomputable opaque rightProgram (ε c : ℚ) (k : ℕ) : Procedure unaryCode ratCode
    (fun N => (endpoints ε (RationalLogScale.value c k N)).2) :=
  Procedure.ratMul.comp
    ((Procedure.constant unaryCode ratCode (1 + ε / 2)).pair (RationalLogScale.program c k))

noncomputable opaque program (ε c : ℚ) (k : ℕ) : Procedure unaryCode
    (prodCode ratCode ratCode) (fun N => endpoints ε (RationalLogScale.value c k N)) :=
  (leftProgram ε c k).pair (rightProgram ε c k)

noncomputable def certificate (ε c : ℚ) (k : ℕ) :
    Turing.TM2ComputableInPolyTime unaryCode (prodCode ratCode ratCode)
      (fun N => endpoints ε (RationalLogScale.value c k N)) :=
  (program ε c k).toTM2

end ContinuumCoulomb.CalibrationRationalBracket

end OAI
