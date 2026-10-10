import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombPairEvaluation

namespace OAI

/-! Polynomial-time rational evaluation of direct Coulomb matrix entries
from their two rational planar coordinates. -/

namespace ContinuumCoulomb.CoulombPairEvaluation
open ExactQuantumFactoring.BitStackProgram

def pointCode : (ℚ×ℚ) → List Bool := prodCode ratCode ratCode
def pairCode : ((ℚ×ℚ)×(ℚ×ℚ)) → List Bool := prodCode pointCode pointCode
abbrev Input := ℕ×((ℚ×ℚ)×(ℚ×ℚ))
def inputCode : Input → List Bool := prodCode unaryCode pairCode

noncomputable opaque squaredDistanceProgram : Procedure pairCode ratCode
    (fun x => squaredDistance x.1 x.2) := by
  let a := Procedure.first pointCode pointCode
  let b := Procedure.second pointCode pointCode
  let ax := (Procedure.first ratCode ratCode).comp a
  let ay := (Procedure.second ratCode ratCode).comp a
  let bx := (Procedure.first ratCode ratCode).comp b
  let byCoord := (Procedure.second ratCode ratCode).comp b
  let dx := Procedure.ratSub.comp (ax.pair bx)
  let dy := Procedure.ratSub.comp (ay.pair byCoord)
  let xx := Procedure.ratMul.comp (dx.pair dx)
  let yy := Procedure.ratMul.comp (dy.pair dy)
  exact (Procedure.ratAdd.comp (xx.pair yy)).congrFun
    (by intro x; simp only [squaredDistance,pow_two]; rfl)

noncomputable opaque precisionProgram : Procedure unaryCode unaryCode precision :=
  (ResolventSchedule.mulProgram.comp ((Procedure.constant unaryCode unaryCode 2).pair
    Procedure.unarySuccessor)).congrFun (by intro P; rfl)

noncomputable opaque rootPrecisionProgram (rho : ℕ) : Procedure unaryCode unaryCode (rootPrecision rho) :=
  (ResolventSchedule.mulProgram.comp
    ((Procedure.constant unaryCode unaryCode (4*lipschitzGuard rho)).pair
      Procedure.unarySuccessor)).congrFun (by intro P; rfl)

noncomputable opaque distanceProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => distance rho x.1 x.2.1 x.2.2) :=
  (RationalSquareRoot.program.comp
    (((rootPrecisionProgram rho).comp (Procedure.first unaryCode pairCode)).pair
      (squaredDistanceProgram.comp (Procedure.second unaryCode pairCode)))).congrFun (by intro x; rfl)

noncomputable opaque program (rho : ℕ) : Procedure inputCode ratCode
    (fun x => approximate rho x.1 x.2.1 x.2.2) :=
  ((CoulombEvaluation.program rho).comp
    ((precisionProgram.comp (Procedure.first unaryCode pairCode)).pair
      (distanceProgram rho))).congrFun (by intro x; rfl)

noncomputable def certificate (rho : ℕ) : Turing.TM2ComputableInPolyTime inputCode ratCode
    (fun x => approximate rho x.1 x.2.1 x.2.2) := (program rho).toTM2

end ContinuumCoulomb.CoulombPairEvaluation

end OAI
