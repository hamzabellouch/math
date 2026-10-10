import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombPairSum
import OAI.Computability.QuantumFactoring.NativeAIGAddWrapper

namespace OAI

/-! The direct-interaction scalar uses two literal finite list traversals;
its precision increases only polynomially with the number of sites. -/

namespace ContinuumCoulomb.CoulombPairSum
open ExactQuantumFactoring.BitStackProgram

def pointCode : Point → List Bool := CoulombPairEvaluation.pointCode
def inputCode : Input → List Bool := prodCode unaryCode (listCode pointCode)
def rowCode : (ℕ×(Point×List Point)) → List Bool :=
  prodCode unaryCode (prodCode pointCode (listCode pointCode))

noncomputable opaque offsiteProgram (rho : ℕ) :
    Procedure CoulombPairEvaluation.inputCode ratCode
      (fun x => offsite rho x.1 x.2.1 x.2.2) := by
  let pairs := Procedure.second unaryCode CoulombPairEvaluation.pairCode
  let dist := CoulombPairEvaluation.squaredDistanceProgram.comp pairs
  let test := Procedure.binaryZero.comp (Procedure.intAbs.comp (Procedure.ratNum.comp dist))
  let zero := Procedure.constant CoulombPairEvaluation.inputCode ratCode (0:ℚ)
  exact (Procedure.conditional test zero (CoulombPairEvaluation.program rho)).congrFun (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq,Int.natAbs_eq_zero,Rat.num_eq_zero,offsite])

noncomputable opaque offsiteEnvironmentProgram (rho : ℕ) :
    Procedure (prodCode (prodCode unaryCode pointCode) pointCode) ratCode
      (fun x => offsite rho x.1.1 x.1.2 x.2) := by
  let env := Procedure.first (prodCode unaryCode pointCode) pointCode
  let p := (Procedure.first unaryCode pointCode).comp env
  let a := (Procedure.second unaryCode pointCode).comp env
  let b := Procedure.second (prodCode unaryCode pointCode) pointCode
  exact (offsiteProgram rho).comp (p.pair (a.pair b))

noncomputable opaque rowProgram (rho : ℕ) : Procedure rowCode ratCode
    (fun x => row rho x.1 x.2.1 x.2.2) := by
  let p := Procedure.first unaryCode (prodCode pointCode (listCode pointCode))
  let tail := Procedure.second unaryCode (prodCode pointCode (listCode pointCode))
  let a := (Procedure.first pointCode (listCode pointCode)).comp tail
  let sites := (Procedure.second pointCode (listCode pointCode)).comp tail
  let mapped := (Procedure.listMapWith (ea := prodCode unaryCode pointCode)
    (eb := pointCode) (ec := ratCode)
    (f := fun env b => offsite rho env.1 env.2 b) (0,0) 0
    (offsiteEnvironmentProgram rho)).comp ((p.pair a).pair sites)
  exact (RationalSumProgram.sumProgram.comp mapped).congrFun (by intro x; rfl)

noncomputable opaque rowEnvironmentProgram (rho : ℕ) :
    Procedure (prodCode inputCode pointCode) ratCode (fun x => row rho x.1.1 x.2 x.1.2) := by
  let env := Procedure.first inputCode pointCode
  let p := (Procedure.first unaryCode (listCode pointCode)).comp env
  let sites := (Procedure.second unaryCode (listCode pointCode)).comp env
  let a := Procedure.second inputCode pointCode
  exact (rowProgram rho).comp (p.pair (a.pair sites))

noncomputable opaque totalProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => total rho x.1 x.2) := by
  let sites := Procedure.second unaryCode (listCode pointCode)
  let mapped := (Procedure.listMapWith (ea := inputCode) (eb := pointCode) (ec := ratCode)
    (f := fun env a => row rho env.1 a env.2) (0,0) 0
    (rowEnvironmentProgram rho)).comp ((Procedure.identity inputCode).pair sites)
  let sum := RationalSumProgram.sumProgram.comp mapped
  exact (Procedure.ratDiv.comp (sum.pair (Procedure.constant inputCode ratCode 2))).congrFun
    (by intro x; rfl)

noncomputable opaque lengthProgram : Procedure inputCode unaryCode (fun x => x.2.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pointCode (0,0)).comp
    (Procedure.second unaryCode (listCode pointCode))

noncomputable opaque precisionProgram : Procedure inputCode unaryCode
    (fun x => precision x.2.length x.1) := by
  let msq := ResolventSchedule.squareProgram.comp (Procedure.unarySuccessor.comp lengthProgram)
  let pp := Procedure.unarySuccessor.comp (Procedure.first unaryCode (listCode pointCode))
  exact (ResolventSchedule.mulProgram.comp (msq.pair pp)).congrFun (by intro x; rfl)

noncomputable opaque argumentProgram : Procedure inputCode inputCode
    (fun x => (precision x.2.length x.1,x.2)) :=
  precisionProgram.pair (Procedure.second unaryCode (listCode pointCode))

noncomputable opaque program (rho : ℕ) : Procedure inputCode ratCode (value rho) := by
  let p := (totalProgram rho).comp argumentProgram
  exact p.congrFun (by intro x; rfl)

noncomputable def certificate (rho : ℕ) : Turing.TM2ComputableInPolyTime inputCode ratCode
    (value rho) := (program rho).toTM2

end ContinuumCoulomb.CoulombPairSum

end OAI
