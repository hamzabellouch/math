import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorFluid
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ViscosityScaling
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularForce

namespace OAI

/-! Rescaling physical time and only the horizontal velocity gives the
same scalar observation threshold at every positive viscosity. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem viscosityDrift_periodic {a : ℝ → Plane → Plane}
    (ha : ∀ t, PlanePeriodic (a t)) (ν : ℝ) :
    ∀ t, PlanePeriodic (viscosityDrift ν a t) := by
  intro t x k
  simp only [viscosityDrift, ha (ν * t) x k]

theorem viscosityDrift_divergence {a : ℝ → Plane → Plane}
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hd : ∀ t x, PlanarHamiltonian.divergence (a t) x = 0) (ν : ℝ) (t : ℝ) (x : Plane) :
    PlanarHamiltonian.divergence (viscosityDrift ν a t) x = 0 := by
  have hs : ContDiff ℝ ∞ (a (ν * t)) := ha.comp (contDiff_const.prodMk contDiff_id)
  have h := divergence_scalar_product hs (contDiff_const (c := ν)) x
  change PlanarHamiltonian.divergence (fun y => ν • a (ν * t) y) x = 0
  simpa only [hd, mul_zero, fderiv_const_apply, zero_apply, add_zero] using h

def detectorViscosityForce (V : ℝ → Plane → Plane) (C L : ℕ) (ν : ℝ) : Velocity :=
  triangularForce ν (viscosityDrift ν (detectorDrift V C L))
    (viscositySource ν (detectorSource C L))

theorem detectorViscosity_solution
    {V : ℝ → Plane → Plane} (hV : ContDiff ℝ ∞ (Function.uncurry V))
    (hp : ∀ t, PlanePeriodic (V t))
    (hd : ∀ t x, PlanarHamiltonian.divergence (V t) x = 0)
    (C L : ℕ) {w : ℝ → Plane → ℝ}
    (hs : GlobalTorusScalarSolution 1 (detectorDrift V C L) (detectorSource C L)
      w (fun _ => 0)) (hw : ContDiff ℝ ∞ (Function.uncurry w))
    (hwp : ∀ t, PlanePeriodic (w t)) {ν : ℝ} (hν : 0 < ν) :
    IsClassicalSolution 1 ν (detectorViscosityForce V C L ν)
      (triangularVelocity (viscosityDrift ν (detectorDrift V C L)) (viscosityScalar ν w))
      (fun _ => 0) := by
  exact triangularVelocity_solution (viscosityDrift_smooth (detectorDrift_smooth hV C L) ν)
    (viscosityScalar_smooth hw ν) (hs.viscosity hw hν.le)
    (viscosityDrift_periodic (detectorDrift_periodic hp C L) ν)
    (fun t => hwp (ν * t))
    (viscosityDrift_divergence (detectorDrift_smooth hV C L)
      (detectorDrift_divergence hV hd C L) ν)
    (fun x => by simp only [viscosityDrift, mul_zero,
      detectorDrift_before V C L le_rfl x, smul_zero])

theorem viscosityScalar_observation {w : ℝ → Plane → ℝ} {ν : ℝ} (hν : 0 < ν)
    (E : Set Plane) :
    (∃ t, 0 ≤ t ∧ ∃ x ∈ E, 1 / 2 < viscosityScalar ν w t x) ↔
      ∃ t, 0 ≤ t ∧ ∃ x ∈ E, 1 / 2 < w t x := by
  constructor
  · rintro ⟨t, ht, x, hx, hh⟩
    exact ⟨ν * t, mul_nonneg hν.le ht, x, hx, hh⟩
  · rintro ⟨t, ht, x, hx, hh⟩
    refine ⟨t / ν, div_nonneg ht hν.le, x, hx, ?_⟩
    have he : ν * (t / ν) = t := by field_simp [hν.ne']
    simpa only [viscosityScalar, he] using hh

end ForcedComputation.VelocityDetector

end

end OAI
