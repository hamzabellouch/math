import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PrefactorCalibration

namespace OAI

/-! The fixed rational prefactor needs only two extra arithmetic operations
before the existing certified calibration program. -/

namespace ContinuumCoulomb.PrefactorCalibration
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque weightProgram (a : ℚ) : Procedure ratCode ratCode (adjustedWeight a) :=
  Procedure.ratDiv.comp ((Procedure.identity ratCode).pair
    (Procedure.constant ratCode ratCode (a^2)))

noncomputable opaque precisionProgram (C : ℕ) : Procedure unaryCode unaryCode (precision C) :=
  Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode C).pair Procedure.unarySuccessor)

noncomputable opaque inputProgram (a : ℚ) (C : ℕ) :
    Procedure AutomaticCalibration.inputCode AutomaticCalibration.inputCode (input a C) := by
  let base := Procedure.first unaryCode (prodCode unaryCode ratCode)
  let tail := Procedure.second unaryCode (prodCode unaryCode ratCode)
  let p := (precisionProgram C).comp ((Procedure.first unaryCode ratCode).comp tail)
  let w := (weightProgram a).comp ((Procedure.second unaryCode ratCode).comp tail)
  exact base.pair (p.pair w)

noncomputable opaque program (rho : ℕ) (a : ℚ) (C : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Procedure AutomaticCalibration.inputCode ratCode (value rho a C ε c k A B) :=
  (AutomaticCalibration.program rho ε c k A B).comp (inputProgram a C)

noncomputable def certificate (rho : ℕ) (a : ℚ) (C : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Turing.TM2ComputableInPolyTime AutomaticCalibration.inputCode ratCode
      (value rho a C ε c k A B) := (program rho a C ε c k A B).toTM2

noncomputable opaque normalizedProgram (rho : ℕ) (a : ℚ) (C : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Procedure AutomaticCalibration.inputCode ratCode (normalizedValue rho a C ε c k A B) :=
  Procedure.ratDiv.comp ((program rho a C ε c k A B).pair
    (AutomaticCalibration.spacingProgram c k))

noncomputable def normalizedCertificate (rho : ℕ) (a : ℚ) (C : ℕ)
    (ε c : ℚ) (k A B : ℕ) :
    Turing.TM2ComputableInPolyTime AutomaticCalibration.inputCode ratCode
      (normalizedValue rho a C ε c k A B) := (normalizedProgram rho a C ε c k A B).toTM2

end ContinuumCoulomb.PrefactorCalibration

end OAI
