import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.AutomaticCalibrationList
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ContactSourceInputProgram

namespace OAI

/-! One literal polynomial-time map from source arrays and target edge
coefficients to the physically scaled rational contact coordinates. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedContactProgram
open ExactQuantumFactoring.BitStackProgram

abbrev Data := List (ℤ × ℤ) × (List MediatorListProgram.Bond × List ℚ)
abbrev Input := ℕ × (AutomaticCalibrationList.Environment × Data)

def dataCode : Data → List Bool :=
  prodCode (listCode ContactCanonicalEdgeProgram.latticeCode)
    (prodCode (listCode MediatorListProgram.bondCode) (listCode ratCode))

def inputCode : Input → List Bool :=
  prodCode unaryCode (prodCode AutomaticCalibrationList.environmentCode dataCode)

def rawInput (rho : ℕ) (ε c : ℚ) (k A B : ℕ) (x : Input) : ContactSourceInputProgram.Input :=
  (x.1, (x.2.2.1, (x.2.2.2.1,
    AutomaticCalibrationList.value rho ε c k A B (x.2.1, x.2.2.2.2))))

def value (rho : ℕ) (ε c : ℚ) (k A B : ℕ) (x : Input) : List (ℚ × ℚ) :=
  ContactSourceInputProgram.scaledPositions
    (AutomaticCalibration.spacing c k x.2.1.1, rawInput rho ε c k A B x)

noncomputable opaque precisionProgram : Procedure inputCode unaryCode Prod.fst :=
  Procedure.first unaryCode _

noncomputable opaque restProgram : Procedure inputCode
    (prodCode AutomaticCalibrationList.environmentCode dataCode) Prod.snd := Procedure.second unaryCode _

noncomputable opaque environmentProgram : Procedure inputCode
    AutomaticCalibrationList.environmentCode (fun x => x.2.1) :=
  (Procedure.first AutomaticCalibrationList.environmentCode dataCode).comp restProgram

noncomputable opaque dataProgram : Procedure inputCode dataCode (fun x => x.2.2) :=
  (Procedure.second AutomaticCalibrationList.environmentCode dataCode).comp restProgram

noncomputable opaque coordinatesProgram : Procedure inputCode
    (listCode ContactCanonicalEdgeProgram.latticeCode) (fun x => x.2.2.1) :=
  (Procedure.first _ _).comp dataProgram

noncomputable opaque listsProgram : Procedure inputCode
    (prodCode (listCode MediatorListProgram.bondCode) (listCode ratCode)) (fun x => x.2.2.2) :=
  (Procedure.second _ _).comp dataProgram

noncomputable opaque bondsProgram : Procedure inputCode
    (listCode MediatorListProgram.bondCode) (fun x => x.2.2.2.1) :=
  (Procedure.first _ _).comp listsProgram

noncomputable opaque coefficientsProgram : Procedure inputCode (listCode ratCode)
    (fun x => x.2.2.2.2) := (Procedure.second _ _).comp listsProgram

noncomputable opaque lengthsProgram (rho : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Procedure inputCode (listCode ratCode)
      (fun x => AutomaticCalibrationList.value rho ε c k A B (x.2.1, x.2.2.2.2)) :=
  (AutomaticCalibrationList.program rho ε c k A B).comp
    (environmentProgram.pair coefficientsProgram)

noncomputable opaque rawProgram (rho : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Procedure inputCode ContactSourceInputProgram.inputCode (rawInput rho ε c k A B) :=
  precisionProgram.pair (coordinatesProgram.pair
    (bondsProgram.pair (lengthsProgram rho ε c k A B)))

noncomputable opaque spacingProgram (c : ℚ) (k : ℕ) : Procedure inputCode ratCode
    (fun x => AutomaticCalibration.spacing c k x.2.1.1) :=
  (RationalLogScale.program c k).comp
    ((Procedure.first unaryCode unaryCode).comp environmentProgram)

noncomputable opaque program (rho : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Procedure inputCode (listCode ContactRationalGadget.pointCode) (value rho ε c k A B) :=
  ContactSourceInputProgram.scaledProgram.comp
    ((spacingProgram c k).pair (rawProgram rho ε c k A B))

noncomputable def certificate (rho : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Turing.TM2ComputableInPolyTime inputCode (listCode ContactRationalGadget.pointCode)
      (value rho ε c k A B) := (program rho ε c k A B).toTM2

end ContinuumCoulomb.CalibratedContactProgram

end

end OAI
