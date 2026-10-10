import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.EulerRegisters

namespace OAI

/-! Rational vector arithmetic and bounded rounding for the three Euler
registers. These are literal finite compositions of integer and rational
stack programs. -/

namespace ContinuumCoulomb.EulerRegisters
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode)

def pointInputCode : (ℕ×Registers) → List Bool := prodCode Nat.bits registersCode
def proposalCode : (ℚ×(Triple×Triple)) → List Bool := prodCode ratCode (prodCode tripleCode tripleCode)
def roundInputCode : ((ℕ×ℕ)×Triple) → List Bool := prodCode (prodCode Nat.bits Nat.bits) tripleCode

noncomputable opaque pointDenominatorProgram : Procedure pointInputCode ratCode
    (fun x => (x.1:ℚ)) := Procedure.natToRat.comp (Procedure.first Nat.bits registersCode)
noncomputable opaque pointRegistersProgram : Procedure pointInputCode registersCode Prod.snd :=
  Procedure.second Nat.bits registersCode
noncomputable opaque firstRegisterProgram : Procedure registersCode intCode Prod.fst :=
  Procedure.first intCode (prodCode intCode intCode)
noncomputable opaque tailRegisterProgram : Procedure registersCode (prodCode intCode intCode) Prod.snd :=
  Procedure.second intCode (prodCode intCode intCode)
noncomputable opaque secondRegisterProgram : Procedure registersCode intCode (fun r => r.2.1) :=
  (Procedure.first intCode intCode).comp tailRegisterProgram
noncomputable opaque thirdRegisterProgram : Procedure registersCode intCode (fun r => r.2.2) :=
  (Procedure.second intCode intCode).comp tailRegisterProgram

noncomputable opaque pointFirstProgram : Procedure pointInputCode ratCode (fun x => (x.2.1:ℚ)/x.1) :=
  Procedure.ratDiv.comp ((Procedure.intToRat.comp (firstRegisterProgram.comp pointRegistersProgram)).pair
    pointDenominatorProgram)
noncomputable opaque pointSecondProgram : Procedure pointInputCode ratCode (fun x => (x.2.2.1:ℚ)/x.1) :=
  Procedure.ratDiv.comp ((Procedure.intToRat.comp (secondRegisterProgram.comp pointRegistersProgram)).pair
    pointDenominatorProgram)
noncomputable opaque pointThirdProgram : Procedure pointInputCode ratCode (fun x => (x.2.2.2:ℚ)/x.1) :=
  Procedure.ratDiv.comp ((Procedure.intToRat.comp (thirdRegisterProgram.comp pointRegistersProgram)).pair
    pointDenominatorProgram)

noncomputable opaque pointProgram : Procedure pointInputCode tripleCode (fun x => point x.1 x.2) :=
  pointFirstProgram.pair (pointSecondProgram.pair pointThirdProgram)

noncomputable opaque tripleFirstProgram : Procedure tripleCode ratCode Prod.fst :=
  Procedure.first ratCode (prodCode ratCode ratCode)
noncomputable opaque tripleTailProgram : Procedure tripleCode (prodCode ratCode ratCode) Prod.snd :=
  Procedure.second ratCode (prodCode ratCode ratCode)
noncomputable opaque tripleSecondProgram : Procedure tripleCode ratCode (fun q => q.2.1) :=
  (Procedure.first ratCode ratCode).comp tripleTailProgram
noncomputable opaque tripleThirdProgram : Procedure tripleCode ratCode (fun q => q.2.2) :=
  (Procedure.second ratCode ratCode).comp tripleTailProgram

noncomputable opaque proposalStepProgram : Procedure proposalCode ratCode Prod.fst :=
  Procedure.first ratCode (prodCode tripleCode tripleCode)
noncomputable opaque proposalPairProgram : Procedure proposalCode (prodCode tripleCode tripleCode) Prod.snd :=
  Procedure.second ratCode (prodCode tripleCode tripleCode)
noncomputable opaque proposalPointProgram : Procedure proposalCode tripleCode (fun x => x.2.1) :=
  (Procedure.first tripleCode tripleCode).comp proposalPairProgram
noncomputable opaque proposalVelocityProgram : Procedure proposalCode tripleCode (fun x => x.2.2) :=
  (Procedure.second tripleCode tripleCode).comp proposalPairProgram

noncomputable opaque proposalCoordinateProgram {f : Triple → ℚ} (p : Procedure tripleCode ratCode f) :
    Procedure proposalCode ratCode (fun x => f x.2.1+x.1*f x.2.2) := by
  let a := p.comp proposalPointProgram
  let b := p.comp proposalVelocityProgram
  exact Procedure.ratAdd.comp (a.pair (Procedure.ratMul.comp (proposalStepProgram.pair b)))

noncomputable opaque proposalProgram : Procedure proposalCode tripleCode
    (fun x => proposal x.1 x.2.1 x.2.2) :=
  (proposalCoordinateProgram tripleFirstProgram).pair
    ((proposalCoordinateProgram tripleSecondProgram).pair (proposalCoordinateProgram tripleThirdProgram))

noncomputable opaque roundParametersProgram : Procedure roundInputCode (prodCode Nat.bits Nat.bits) Prod.fst :=
  Procedure.first (prodCode Nat.bits Nat.bits) tripleCode
noncomputable opaque roundPointProgram : Procedure roundInputCode tripleCode Prod.snd :=
  Procedure.second (prodCode Nat.bits Nat.bits) tripleCode

noncomputable opaque roundCoordinateProgram {f : Triple → ℚ} (p : Procedure tripleCode ratCode f) :
    Procedure roundInputCode intCode (fun x => RationalBoxRound.numerator x.1.1 x.1.2 (f x.2)) :=
  RationalBoxRound.numeratorProgram.comp (roundParametersProgram.pair (p.comp roundPointProgram))

noncomputable opaque roundProgram : Procedure roundInputCode registersCode
    (fun x => round x.1.1 x.1.2 x.2) :=
  (roundCoordinateProgram tripleFirstProgram).pair
    ((roundCoordinateProgram tripleSecondProgram).pair (roundCoordinateProgram tripleThirdProgram))

end ContinuumCoulomb.EulerRegisters

end OAI
