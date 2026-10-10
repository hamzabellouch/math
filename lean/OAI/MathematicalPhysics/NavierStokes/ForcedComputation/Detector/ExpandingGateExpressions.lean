import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingCenterExpressions
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingGateMotion
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarDerivativeBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularLift

namespace OAI

/-! Finite expressions for the actual moving Hamiltonian gates, including
all collar terms. The center velocity is differentiated from its code. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows
open scoped ContDiff

def displacementCode (a T S S' : ℚ) (k target : ℕ) (terminal : Bool)
    (j : Fin 2) : NonperiodicExpr :=
  .sub (.coord j.castSucc.succ) (centerCode a T S S' k target terminal j)

theorem displacementCode_val (a T S S' : ℚ) (k target : ℕ) (terminal : Bool)
    (j : Fin 2) (y : SpaceTime) :
    (displacementCode a T S S' k target terminal j).val y =
      (horizontalLinear y.2 - scheduledCenter a T S S' k target terminal y.1) j := by
  simp only [displacementCode, NonperiodicExpr.sub, NonperiodicExpr.val,
    centerCode_val, Pi.sub_apply]
  have hc : timeSpaceCoord j.castSucc.succ y = horizontalLinear y.2 j := by
    simp only [timeSpaceCoord, Fin.cases_succ]
    rfl
  rw [hc]
  simp only [Rat.cast_neg, Rat.cast_one, neg_one_mul, sub_eq_add_neg]

def gateCutoffCode (R : ℚ) (z : Fin 2 → NonperiodicExpr) : NonperiodicExpr :=
  .mul (NonperiodicExpr.composeProfile (.cutoff (-3) (-2) 2 3) (.mul (.const R⁻¹) (z 0)))
    (NonperiodicExpr.composeProfile (.cutoff (-3) (-2) 2 3) (.mul (.const R⁻¹) (z 1)))

theorem gateCutoffCode_val (R : ℚ) (z : Fin 2 → NonperiodicExpr) (y : SpaceTime) :
    (gateCutoffCode R z).val y = gateCutoff R (fun j => (z j).val y) := by
  have he : gateCutoff R (fun j => (z j).val y) =
      closedCutoff (-3) (-2) 2 3 ((z 0).val y / R) *
      closedCutoff (-3) (-2) 2 3 ((z 1).val y / R) := by
    exact gateCutoff_eq_profiles R (fun j => (z j).val y)
  rw [he]
  simp only [gateCutoffCode, NonperiodicExpr.val, NonperiodicExpr.val_composeProfile,
    ProfileExpr.val_cutoff, Rat.cast_inv, div_eq_mul_inv]
  congr 1 <;> congr 1 <;> ring

def gatePotentialCode (a T S S' R : ℚ) (k target : ℕ) (terminal : Bool) : NonperiodicExpr :=
  let z := displacementCode a T S S' k target terminal
  .mul (gateCutoffCode R z)
    (.sub (.mul ((centerCode a T S S' k target terminal 0).diff 0) (z 1))
      (.mul ((centerCode a T S S' k target terminal 1).diff 0) (z 0)))

def movingGatePotential (R : ℝ) (c : ℝ → Plane) (t : ℝ) (x : Plane) : ℝ :=
  gateCutoff R (x - c t) * PlanarHamiltonian.translationPotential (deriv c t) (x - c t)

theorem gatePotentialCode_val (a T S S' R : ℚ) (k target : ℕ) (terminal : Bool)
    (y : SpaceTime) :
    (gatePotentialCode a T S S' R k target terminal).val y =
      movingGatePotential R (scheduledCenter a T S S' k target terminal) y.1
        (horizontalLinear y.2) := by
  rcases y with ⟨t, x⟩
  simp only [gatePotentialCode, NonperiodicExpr.val, gateCutoffCode_val,
    displacementCode_val, NonperiodicExpr.sub, centerCode_derivative,
    movingGatePotential, PlanarHamiltonian.translationPotential, Pi.sub_apply, Pi.sub_def]
  ring

theorem movingGatePotential_smooth (R : ℝ) {c : ℝ → Plane}
    (hc : ContDiff ℝ ∞ c) : ContDiff ℝ ∞ (Function.uncurry (movingGatePotential R c)) := by
  have hv : ContDiff ℝ ∞ (deriv c) := (contDiff_infty_iff_deriv.mp hc).2
  have hz : ContDiff ℝ ∞ (fun y : ℝ × Plane => y.2 - c y.1) :=
    contDiff_snd.sub (hc.comp contDiff_fst)
  exact ((gateCutoff_smooth R).comp hz).mul
    ((((contDiff_apply ℝ ℝ 0).comp hv).comp contDiff_fst).mul
      ((contDiff_apply ℝ ℝ 1).comp hz) |>.sub
        ((((contDiff_apply ℝ ℝ 1).comp hv).comp contDiff_fst).mul
          ((contDiff_apply ℝ ℝ 0).comp hz)))

private def horizontalSpaceTime : SpaceTime →L[ℝ] (ℝ × Plane) :=
  (ContinuousLinearMap.fst ℝ ℝ Space).prod
    (horizontalLinear.comp (ContinuousLinearMap.snd ℝ ℝ Space))

theorem expression_spatial_lift {e : NonperiodicExpr} {H : ℝ → Plane → ℝ}
    (hH : ContDiff ℝ ∞ (Function.uncurry H))
    (he : ∀ y, e.val y = H y.1 (horizontalLinear y.2))
    (j : Fin 2) (y : SpaceTime) :
    (e.diff j.castSucc.succ).val y =
      PlanarHamiltonian.spatialD j (H y.1) (horizontalLinear y.2) := by
  have heq : e.val = (Function.uncurry H) ∘ horizontalSpaceTime := funext he
  rw [e.val_diff, heq,
    fderiv_comp y (hH.differentiable (by simp) _) horizontalSpaceTime.differentiableAt,
    horizontalSpaceTime.fderiv]
  have hd : horizontalSpaceTime (spaceTimeDirection j.castSucc.succ) =
      (0, PlanarHamiltonian.basis j) := by
    rw [spaceTimeDirection, Fin.cases_succ]
    change ((0 : ℝ), horizontalLinear (ShearFlows.basis j.castSucc)) =
      (0, PlanarHamiltonian.basis j)
    rw [VelocityDetector.horizontalLinear_basis]
  change fderiv ℝ (Function.uncurry H) _
    (horizontalSpaceTime (spaceTimeDirection j.castSucc.succ)) = _
  rw [hd]
  have hs := (hH.differentiable (by simp) (y.1, horizontalLinear y.2)).hasFDerivAt.comp
    (horizontalLinear y.2)
    ((hasFDerivAt_const (𝕜 := ℝ) y.1 (horizontalLinear y.2)).prodMk (hasFDerivAt_id _))
  change _ = fderiv ℝ (H y.1) (horizontalLinear y.2) (PlanarHamiltonian.basis j)
  have hsf : fderiv ℝ (H y.1) (horizontalLinear y.2) =
      (fderiv ℝ (Function.uncurry H) (y.1, horizontalLinear y.2)).comp
        ((0 : Plane →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Plane)) := hs.fderiv
  rw [hsf]
  rfl

def movingGateCode (a T S S' R : ℚ) (k target : ℕ) (terminal : Bool) : NonperiodicVector :=
  let H := gatePotentialCode a T S S' R k target terminal
  fun j => if j = 0 then H.diff 2 else if j = 1 then .mul (.const (-1)) (H.diff 1)
    else .const 0

theorem movingGateCode_val (a T S S' R : ℚ) (k target : ℕ) (terminal : Bool)
    (y : SpaceTime) :
    (movingGateCode a T S S' R k target terminal).val y =
      planeInclusion (movingGate R (scheduledCenter a T S S' k target terminal)
        y.1 (horizontalLinear y.2)) := by
  have he (j : Fin 2) := expression_spatial_lift
    (movingGatePotential_smooth R (scheduledCenter_smooth _ _ _ _ _ _ _))
    (gatePotentialCode_val a T S S' R k target terminal) j y
  have he0 := he 0
  have he1 := he 1
  change ((gatePotentialCode a T S S' R k target terminal).diff 1).val y = _ at he0
  change ((gatePotentialCode a T S S' R k target terminal).diff 2).val y = _ at he1
  funext j
  fin_cases j <;> simp [movingGateCode, NonperiodicVector.val, NonperiodicExpr.val,
    he0, he1, movingGate, translationGate, PlanarHamiltonian.field,
    planeInclusion] <;> rfl

end ForcedComputation.ExpandingDetector

end

end OAI
