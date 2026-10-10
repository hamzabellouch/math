import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NonperiodicResidual
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneUnitImpulse
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarDerivativeBounds

namespace OAI

/-! A finite expression for the normalized compact source. Its integral
is already proved to be one; evaluation uses only the explicit pulse. -/

namespace ForcedComputation.ExpandingDetector
open ShearFlows

def pulseCode (e : NonperiodicExpr) : NonperiodicExpr :=
  NonperiodicExpr.composeProfile (ProfileExpr.ramp 0 1).diff e

theorem pulseCode_val (e : NonperiodicExpr) (y : SpaceTime) :
    (pulseCode e).val y = smoothPulse 0 1 (e.val y) := by
  rw [pulseCode, NonperiodicExpr.val_composeProfile, ProfileExpr.val_diff,
    ProfileExpr.val_ramp]
  simp only [Rat.cast_zero, Rat.cast_one, smoothPulse]

def impulseAxisCode (c : ℚ) (j : Fin 2) : NonperiodicExpr :=
  pulseCode (.add (.sub (.coord j.castSucc.succ) (.const c)) (.const (1 / 2)))

theorem impulseAxisCode_val (c : ℚ) (j : Fin 2) (y : SpaceTime) :
    (impulseAxisCode c j).val y = impulseProfile c (horizontalLinear y.2 j) := by
  have hc : timeSpaceCoord j.castSucc.succ y = horizontalLinear y.2 j := by
    simp only [timeSpaceCoord, Fin.cases_succ]
    rfl
  rw [impulseAxisCode, pulseCode_val]
  change smoothPulse 0 1 (_ + _) = _
  simp only [NonperiodicExpr.val, NonperiodicExpr.sub, impulseProfile,
    Rat.cast_neg, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat, hc]
  congr 1
  ring

def unitImpulseCode (p : Fin 2 → ℚ) : NonperiodicExpr :=
  .mul (pulseCode (.coord 0)) (.mul (impulseAxisCode (p 0) 0) (impulseAxisCode (p 1) 1))

theorem unitImpulseCode_val (p : Fin 2 → ℚ) (y : SpaceTime) :
    (unitImpulseCode p).val y = unitImpulse (fun j => (p j : ℝ)) y.1 (horizontalLinear y.2) := by
  simp only [unitImpulseCode, NonperiodicExpr.val, pulseCode_val, impulseAxisCode_val,
    unitImpulse, spatialImpulse, Fin.prod_univ_two]
  rfl

def verticalSourceCode (p : Fin 2 → ℚ) : NonperiodicVector :=
  fun j => if j = 2 then unitImpulseCode p else .const 0

theorem verticalSourceCode_val (p : Fin 2 → ℚ) (y : SpaceTime) :
    (verticalSourceCode p).val y =
      unitImpulse (fun j => (p j : ℝ)) y.1 (horizontalLinear y.2) • basis 2 := by
  funext j
  fin_cases j <;> simp [NonperiodicVector.val, verticalSourceCode, NonperiodicExpr.val,
    unitImpulseCode_val,
    ShearFlows.basis]

end ForcedComputation.ExpandingDetector

end OAI
