import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Regularity
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ForceEvaluation

namespace OAI

/-! Exact ordered mixed derivatives under multiplication of physical time.
This is the time part of the detector's viscosity rescaling. -/

noncomputable section
namespace ForcedComputation
open ShearFlows
open scoped ContDiff

def scaledTimeLinear (ν : ℝ) : SpaceTime →L[ℝ] SpaceTime :=
  (ν • ContinuousLinearMap.fst ℝ ℝ Space).prod (ContinuousLinearMap.snd ℝ ℝ Space)

theorem scaledTimeLinear_apply (ν : ℝ) (y : SpaceTime) :
    scaledTimeLinear ν y = (ν * y.1, y.2) := rfl

theorem scaledTimeLinear_direction (ν : ℝ) (j : Fin 4) :
    scaledTimeLinear ν (spaceTimeDirection j) =
      (if j = 0 then ν else 1) • spaceTimeDirection j := by
  cases j using Fin.cases with
  | zero => simp [scaledTimeLinear, spaceTimeDirection, Prod.smul_mk]
  | succ k => simp [scaledTimeLinear, spaceTimeDirection]

def velocityTimeScale (ν : ℝ) (V : Velocity) : Velocity := V ∘ scaledTimeLinear ν

theorem velocityTimeScale_smooth {V : Velocity} (hV : ContDiff ℝ ∞ V) (ν : ℝ) :
    ContDiff ℝ ∞ (velocityTimeScale ν V) :=
  hV.comp (scaledTimeLinear ν).contDiff

theorem velocityTimeScale_derivative {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (ν : ℝ) (j : Fin 4) (y : SpaceTime) :
    fderiv ℝ (velocityTimeScale ν V) y (spaceTimeDirection j) =
      (if j = 0 then ν else 1) •
        fderiv ℝ V (scaledTimeLinear ν y) (spaceTimeDirection j) := by
  rw [velocityTimeScale, fderiv_comp y (hV.differentiable (by simp) _)
    (scaledTimeLinear ν).differentiableAt, (scaledTimeLinear ν).fderiv,
    ContinuousLinearMap.comp_apply, scaledTimeLinear_direction, map_smul]

theorem mixedDerivative_velocityTimeScale {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (ν : ℝ) (α : List (Fin 4)) :
    mixedDerivative (velocityTimeScale ν V) α =
      ν ^ α.count 0 • velocityTimeScale ν (mixedDerivative V α) := by
  induction α with
  | nil => simp only [mixedDerivative, List.count_nil, pow_zero, one_smul]
  | cons j α ih =>
    funext y
    change fderiv ℝ (mixedDerivative (velocityTimeScale ν V) α) y
      (spaceTimeDirection j) = _
    rw [ih, fderiv_const_smul
      ((velocityTimeScale_smooth (mixedDerivative_smooth hV α) ν).differentiable (by simp) y),
      smul_apply,
      velocityTimeScale_derivative (mixedDerivative_smooth hV α)]
    by_cases hj : j = 0
    · subst j
      simp only [ite_true, List.count_cons_self, pow_succ, smul_smul]
      rfl
    · simp only [hj, ite_false, one_smul, List.count_cons_of_ne hj]
      rfl

theorem mixedDerivative_clm {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (A : Space →L[ℝ] Space) (α : List (Fin 4)) :
    mixedDerivative (A ∘ V) α = A ∘ mixedDerivative V α := by
  induction α with
  | nil => rfl
  | cons j α ih =>
    funext y
    change fderiv ℝ (mixedDerivative (A ∘ V) α) y (spaceTimeDirection j) = _
    rw [ih, fderiv_comp y A.differentiableAt
      ((mixedDerivative_smooth hV α).differentiable (by simp) y), A.fderiv]
    rfl

end ForcedComputation

end

end OAI
