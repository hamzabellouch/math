import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularFluid
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.StationaryBounds

namespace OAI

/-! Regularity of the force follows from the explicit planar residual.
No regularity of the unknown transported scalar is needed to prescribe it. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows
open scoped ContDiff

theorem triangularForce_eq_residual {a : ℝ → Plane → Plane}
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (h : ℝ → Plane → ℝ) (ν : ℝ) :
    triangularForce ν a h = residual ν (triangularVelocity a (fun _ _ => 0)) +
      triangularVelocity (fun _ _ => 0) h := by
  funext y
  have has : ContDiff ℝ ∞ (a y.1) := ha.comp (contDiff_const.prodMk contDiff_id)
  change _ = residual ν (triangularVelocity a (fun _ _ => 0)) (y.1, y.2) + _
  unfold residual
  rw [triangularVelocity_timeDerivative ha contDiff_const,
    show (fun z => triangularVelocity a (fun _ _ => 0) (y.1, z)) =
      triangularLift (a y.1) (fun _ => 0) from rfl,
    triangularLift_advection has contDiff_const, triangularLift_laplacian has contDiff_const]
  simp only [triangularForce, triangularVelocity, triangularLift, planarResidual,
    scalarLaplacian_zero, fderiv_const_apply, zero_apply, deriv_const,
    map_add, map_sub, map_smul, map_zero, zero_smul, add_zero, zero_add]

theorem triangularForce_smooth {a : ℝ → Plane → Plane} {h : ℝ → Plane → ℝ}
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (ν : ℝ) :
    ContDiff ℝ ∞ (triangularForce ν a h) := by
  rw [triangularForce_eq_residual ha]
  exact (residual_smooth (triangularVelocity_smooth ha contDiff_const) ν).add
    (triangularVelocity_smooth contDiff_const hh)

theorem triangularForce_periodic {a : ℝ → Plane → Plane} {h : ℝ → Plane → ℝ}
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hpa : ∀ t, PlanePeriodic (a t)) (hph : ∀ t, PlanePeriodic (h t)) (ν : ℝ) :
    SpatiallyPeriodic 1 (triangularForce ν a h) := by
  rw [triangularForce_eq_residual ha]
  have hr := residual_spatially_periodic (triangularVelocity_smooth ha contDiff_const)
    (triangularVelocity_periodic hpa
      (show ∀ t, PlanePeriodic (fun _ : Plane => (0 : ℝ)) from fun _ _ _ => rfl)) ν
  have hh := triangularVelocity_periodic
    (show ∀ t, PlanePeriodic (fun _ : Plane => (0 : Plane)) from fun _ _ _ => rfl) hph
  intro t x k
  simp only [Pi.add_apply, hr t x k, hh t x k]

end ForcedComputation.VelocityDetector

end

end OAI
