import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorScalar
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorDivergence
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularFluid
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FiniteTimeUniqueness

namespace OAI

/-! The explicit source program has a unique classical fluid realization.
The force is fixed before choosing the scalar solution. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows
open scoped ContDiff

def detectorForce (V : ℝ → Plane → Plane) (C L : ℕ) : Velocity :=
  triangularForce 1 (detectorDrift V C L) (detectorSource C L)

theorem detectorFluid_exists (hE : TorusScalarExistence)
    {V : ℝ → Plane → Plane} (hV : ContDiff ℝ ∞ (Function.uncurry V))
    (hp : ∀ t, PlanePeriodic (V t))
    (hd : ∀ t x, PlanarHamiltonian.divergence (V t) x = 0) (C L : ℕ) :
    ∃ w : ℝ → Plane → ℝ,
      GlobalTorusScalarSolution 1 (detectorDrift V C L) (detectorSource C L) w (fun _ => 0) ∧
      ContDiff ℝ ∞ (Function.uncurry w) ∧
      (∀ t x, 0 ≤ w t x) ∧
      IsClassicalSolution 1 1 (detectorForce V C L)
        (triangularVelocity (detectorDrift V C L) w) (fun _ => 0) ∧
      (∀ u p, IsClassicalSolution 1 1 (detectorForce V C L) u p →
        ∀ t, 0 ≤ t → ∀ x,
          u (t, x) = triangularVelocity (detectorDrift V C L) w (t, x) ∧ p (t, x) = 0) := by
  obtain ⟨w, hs, hw, hwp, hw₀, _⟩ := detectorScalar_exists hE hV hp C L
  have hu := triangularVelocity_solution (detectorDrift_smooth hV C L) hw hs
    (detectorDrift_periodic hp C L) hwp (detectorDrift_divergence hV hd C L)
    (detectorDrift_before V C L le_rfl)
  exact ⟨w, hs, hw, hw₀, hu,
    finite_time_classical_unique (by norm_num) (by norm_num) hu⟩

end ForcedComputation.VelocityDetector

end

end OAI
