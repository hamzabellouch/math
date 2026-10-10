import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NonperiodicResidual
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateClock

namespace OAI

/-! The scheduled centers have finite rational expression codes. Their
formal time derivatives are the actual gate velocities. -/

namespace ForcedComputation.ExpandingDetector
open ShearFlows
open scoped ContDiff

def rampCode (a b : ℚ) : NonperiodicExpr :=
  NonperiodicExpr.composeProfile (ProfileExpr.ramp a b) (.coord 0)

theorem rampCode_val (a b : ℚ) (y : SpaceTime) :
    (rampCode a b).val y = smoothRamp a b y.1 := by
  rw [rampCode, NonperiodicExpr.val_composeProfile, ProfileExpr.val_ramp]
  rfl

def firstWeightCode (a T : ℚ) : NonperiodicExpr := rampCode (a + T / 12) (a + T / 4)
def secondWeightCode (a T : ℚ) : NonperiodicExpr := rampCode (a + 5 * T / 12) (a + 7 * T / 12)
def thirdWeightCode (a T : ℚ) : NonperiodicExpr := rampCode (a + 3 * T / 4) (a + 11 * T / 12)

theorem weightCodes_val (a T : ℚ) (y : SpaceTime) :
    (firstWeightCode a T).val y = firstWeight a T y.1 ∧
    (secondWeightCode a T).val y = secondWeight a T y.1 ∧
    (thirdWeightCode a T).val y = thirdWeight a T y.1 := by
  simp [firstWeightCode, secondWeightCode, thirdWeightCode, rampCode_val,
    firstWeight, secondWeight, thirdWeight]

def centerCode (a T S S' : ℚ) (k target : ℕ) (terminal : Bool) (j : Fin 2) : NonperiodicExpr :=
  if j = 0 then
    .add (.mul (.sub (.const 1) (secondWeightCode a T)) (.const (S * k)))
      (.mul (secondWeightCode a T) (.const (S' * target)))
  else
    .add (.add (.mul (.sub (.const 1) (firstWeightCode a T)) (.const (-S)))
      (.mul (.sub (firstWeightCode a T) (thirdWeightCode a T)) (.const (-((k : ℚ) + 2) * S))))
      (.mul (thirdWeightCode a T) (.const (if terminal then S' else -S')))

theorem centerCode_val (a T S S' : ℚ) (k target : ℕ) (terminal : Bool)
    (j : Fin 2) (y : SpaceTime) :
    (centerCode a T S S' k target terminal j).val y =
      scheduledCenter a T S S' k target terminal y.1 j := by
  obtain ⟨h₁, h₂, h₃⟩ := weightCodes_val a T y
  fin_cases j
  · simp [centerCode, NonperiodicExpr.val, NonperiodicExpr.sub, h₂,
      scheduledCenter, gateCenter]
    ring
  · cases terminal <;> simp [centerCode, NonperiodicExpr.val, NonperiodicExpr.sub, h₁, h₃,
      scheduledCenter, gateCenter] <;> ring

theorem centerCode_derivative (a T S S' : ℚ) (k target : ℕ) (terminal : Bool)
    (j : Fin 2) (t : ℝ) (x : Space) :
    ((centerCode a T S S' k target terminal j).diff 0).val (t,x) =
      deriv (scheduledCenter a T S S' k target terminal) t j := by
  let e := centerCode a T S S' k target terminal j
  have hd := (e.smooth.differentiable (by simp) (t,x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hde : HasDerivAt (fun s => (centerCode a T S S' k target terminal j).val (s,x))
      ((e.diff 0).val (t,x)) t := by
    rw [NonperiodicExpr.val_diff]
    exact hd
  have he : (fun s => (centerCode a T S S' k target terminal j).val (s,x)) =
      fun s => scheduledCenter a T S S' k target terminal s j :=
    funext (fun s => centerCode_val a T S S' k target terminal j (s,x))
  rw [he] at hde
  have hc := ((scheduledCenter_smooth (a : ℝ) T S S' k target terminal).differentiable
    (by simp) t).hasDerivAt
  have hdj := (ContinuousLinearMap.proj j : Plane →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hc
  exact hde.unique hdj

end ForcedComputation.ExpandingDetector

end OAI
