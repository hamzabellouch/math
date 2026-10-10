import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAxisSample
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.MediatorProgram

namespace OAI

/-! Literal polynomial programs for the algebraic four-spin coupling samples. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque valueProgram (a : Fin 2) : Procedure unaryCode ratCode (fun k => value k a) := by
  by_cases ha : a = 0
  · let root := RationalSquareRoot.program.comp
      ((Procedure.identity unaryCode).pair (Procedure.constant unaryCode ratCode 3))
    exact (Procedure.ratMul.comp (root.pair (Procedure.constant unaryCode ratCode (1/384)))).congrFun
      (by intro k; simp only [value,ha,ite_true,Function.comp_apply,id_eq]; ring)
  · exact (Procedure.constant unaryCode ratCode (3/4)).congrFun (by intro k; simp only [value,ha,ite_false])

def radialCode : (ℕ × ℚ) → List Bool := prodCode unaryCode ratCode

noncomputable opaque radicandProgram (a b : Fin 2) :
    Procedure radialCode ratCode (fun x => radicand x.1 a b x.2) := by
  let precision := Procedure.first unaryCode ratCode
  let coefficient := Procedure.second unaryCode ratCode
  let absolute := MediatorProgram.absoluteProgram.comp coefficient
  let factor := Procedure.ratMul.comp ((Procedure.constant radialCode ratCode (8/3)).pair absolute)
  let left := (valueProgram a).comp precision
  let right := (valueProgram b).comp precision
  exact (Procedure.ratMul.comp ((Procedure.ratMul.comp (factor.pair left)).pair right)).congrFun
    (by intro x; rfl)

def couplingCode : (ℕ × (ℕ × ℚ)) → List Bool := prodCode unaryCode (prodCode unaryCode ratCode)

noncomputable opaque couplingProgram (a b : Fin 2) : Procedure couplingCode ratCode
    (fun x => coupling x.1 x.2.1 a b x.2.2) := by
  let inner := Procedure.first unaryCode (prodCode unaryCode ratCode)
  let rest := Procedure.second unaryCode (prodCode unaryCode ratCode)
  let outer := (Procedure.first unaryCode ratCode).comp rest
  let coefficient := (Procedure.second unaryCode ratCode).comp rest
  let argument := (radicandProgram a b).comp (inner.pair coefficient)
  exact (RationalSquareRoot.program.comp (outer.pair argument)).congrFun (by intro x; rfl)

noncomputable def couplingCertificate (a b : Fin 2) : Turing.TM2ComputableInPolyTime
    couplingCode ratCode (fun x => coupling x.1 x.2.1 a b x.2.2) :=
  (couplingProgram a b).toTM2

def calibrated (a b : Fin 2) (x : ℕ × ℚ) : ℚ := coupling (2*x.1+6) x.1 a b x.2

noncomputable opaque inputPrecisionProgram : Procedure radialCode unaryCode Prod.fst :=
  Procedure.first unaryCode ratCode

noncomputable opaque inputCoefficientProgram : Procedure radialCode ratCode Prod.snd :=
  Procedure.second unaryCode ratCode

noncomputable opaque doubledPrecisionProgram : Procedure radialCode unaryCode (fun x => 2*x.1) :=
  Procedure.unaryMul.comp ((Procedure.constant radialCode unaryCode 2).pair inputPrecisionProgram)

noncomputable opaque innerPrecisionProgram : Procedure radialCode unaryCode (fun x => 2*x.1+6) :=
  Procedure.unaryAdd.comp (doubledPrecisionProgram.pair (Procedure.constant radialCode unaryCode 6))

noncomputable opaque calibratedArgumentsProgram : Procedure radialCode couplingCode
    (fun x => (2*x.1+6,x.1,x.2)) :=
  innerPrecisionProgram.pair (inputPrecisionProgram.pair inputCoefficientProgram)

noncomputable opaque calibratedProgram (a b : Fin 2) : Procedure radialCode ratCode (calibrated a b) :=
  ((couplingProgram a b).comp calibratedArgumentsProgram).congrFun (by intro x; rfl)

noncomputable def calibratedCertificate (a b : Fin 2) : Turing.TM2ComputableInPolyTime
    radialCode ratCode (calibrated a b) := (calibratedProgram a b).toTM2

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
