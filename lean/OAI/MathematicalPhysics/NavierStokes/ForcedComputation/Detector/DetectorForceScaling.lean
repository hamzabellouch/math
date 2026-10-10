import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorViscosity
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.VelocityTimeScale

namespace OAI

/-! Exact anisotropic scaling of the prescribed force. The horizontal
equation has two powers of viscosity and the scalar source has one. -/

noncomputable section
namespace ForcedComputation
open ShearFlows
open scoped ContDiff

theorem residual_viscosity_timeScale {V : Velocity} (hV : ContDiff ℝ ∞ V) (ν : ℝ) :
    residual ν (ν • velocityTimeScale ν V) =
      ν ^ 2 • velocityTimeScale ν (residual 1 V) := by
  funext y
  have hτ : HasDerivAt (fun s : ℝ => ν * s) ν y.1 := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id y.1).const_mul ν
  have ht : DifferentiableAt ℝ (fun s => V (s, y.2)) (ν * y.1) :=
    (hV.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) _
  have hr := residual_reparametrization ν hτ (hasDerivAt_const y.1 ν) y.2 ht
  change residual ν (reparametrizedVelocity (fun s => ν * s) (fun _ => ν) V) y = _
  rw [hr]
  simp only [zero_smul, zero_sub, residual, velocityTimeScale, Function.comp_apply,
    scaledTimeLinear_apply, Pi.smul_apply, one_smul, smul_sub, smul_add, smul_smul, pow_two]
  module

namespace VelocityDetector

theorem viscositySource_smooth {h : ℝ → Plane → ℝ}
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (ν : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (viscositySource ν h)) :=
  contDiff_const.mul (viscosityScalar_smooth hh ν)

theorem viscositySource_periodic {h : ℝ → Plane → ℝ}
    (hp : ∀ t, PlanePeriodic (h t)) (ν : ℝ) :
    ∀ t, PlanePeriodic (viscositySource ν h t) := by
  intro t x k
  simp only [viscositySource, hp (ν * t) x k]

def forceViscosityLinear (ν : ℝ) : Space →L[ℝ] Space :=
  ContinuousLinearMap.pi (fun j =>
    (ν ^ (if j = 2 then 1 else 2)) • ContinuousLinearMap.proj j)

theorem forceViscosityLinear_apply (ν : ℝ) (v : Space) (j : Fin 3) :
    forceViscosityLinear ν v j = ν ^ (if j = 2 then 1 else 2) * v j := rfl

theorem triangularForce_viscosity {a : ℝ → Plane → Plane}
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (h : ℝ → Plane → ℝ) (ν : ℝ) :
    triangularForce ν (viscosityDrift ν a) (viscositySource ν h) =
      forceViscosityLinear ν ∘ velocityTimeScale ν (triangularForce 1 a h) := by
  have hv : ContDiff ℝ ∞ (triangularVelocity a (fun _ _ => 0)) :=
    triangularVelocity_smooth ha contDiff_const
  have he : triangularVelocity (viscosityDrift ν a) (fun _ _ => 0) =
      ν • velocityTimeScale ν (triangularVelocity a (fun _ _ => 0)) := by
    funext y
    simp only [triangularVelocity, triangularLift, viscosityDrift, velocityTimeScale,
      Function.comp_apply, scaledTimeLinear_apply, zero_smul, add_zero,
      Pi.smul_apply, map_smul]
  rw [triangularForce_eq_residual (viscosityDrift_smooth ha ν), he,
    residual_viscosity_timeScale hv ν]
  funext y
  have hh (j : Fin 3) :
      residual 1 (triangularVelocity a (fun _ _ => 0)) (ν * y.1, y.2) j =
        planeInclusion (planarResidual 1 a (ν * y.1) (horizontalLinear y.2)) j := by
    have heq := congrFun (congrFun
      (triangularForce_eq_residual ha (fun _ _ => 0) 1) (ν * y.1, y.2)) j
    simpa only [triangularForce, triangularVelocity, triangularLift,
      zero_smul, add_zero, map_zero, zero_add, Pi.add_apply, Pi.zero_apply] using heq.symm
  ext j
  simp only [Pi.add_apply, Pi.smul_apply, velocityTimeScale, Function.comp_apply,
    scaledTimeLinear_apply, forceViscosityLinear_apply, triangularForce,
    triangularVelocity, triangularLift, viscositySource, smul_eq_mul]
  rw [hh]
  fin_cases j <;> simp [planeInclusion, basis]

theorem detectorViscosityForce_eq (V : ℝ → Plane → Plane)
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (C L : ℕ) (ν : ℝ) :
    detectorViscosityForce V C L ν =
      forceViscosityLinear ν ∘ velocityTimeScale ν (detectorForce V C L) :=
  triangularForce_viscosity (detectorDrift_smooth hV C L) (detectorSource C L) ν

theorem mixedDerivative_detectorViscosityForce (V : ℝ → Plane → Plane)
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (C L : ℕ) (ν : ℝ)
    (α : List (Fin 4)) (y : SpaceTime) (j : Fin 3) :
    mixedDerivative (detectorViscosityForce V C L ν) α y j =
      ν ^ (α.count 0 + if j = 2 then 1 else 2) *
        mixedDerivative (detectorForce V C L) α (ν * y.1, y.2) j := by
  have hF : ContDiff ℝ ∞ (detectorForce V C L) :=
    triangularForce_smooth (detectorDrift_smooth hV C L) (detectorSource_smooth C L) 1
  rw [detectorViscosityForce_eq V hV C L ν,
    mixedDerivative_clm (velocityTimeScale_smooth hF ν),
    mixedDerivative_velocityTimeScale hF]
  simp only [Function.comp_apply, forceViscosityLinear_apply, Pi.smul_apply,
    smul_eq_mul, velocityTimeScale, scaledTimeLinear_apply, pow_add]
  ring

end VelocityDetector
end ForcedComputation

end

end OAI
