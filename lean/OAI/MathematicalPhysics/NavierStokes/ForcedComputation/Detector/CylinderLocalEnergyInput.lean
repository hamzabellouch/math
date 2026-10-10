import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderSolution
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarDerivativeBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingMovingCutoff

namespace OAI

/-! Published local energy identity, restricted to the exact cylinder and
the expanding compact cutoffs used here.

F. Gancedo and A. Hidalgo-Torné, On the Cauchy problem for 3D Navier–Stokes
helical vortex filament, Advances in Mathematics 471 (2025), 110268,
proof of Theorem 5.6, equation (5.4), printed p.23 (arXiv:2311.15413).
Only its integration-by-parts identity is retained. The helical uniqueness
theorem is not used. The identity below assumes the strong classical class
and does not assert uniqueness, a cutoff limit, or any detector property.
-/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows ExpandingDetector MeasureTheory

def cylinderWeight (n : ℕ) (x : Plane) : ℝ :=
  concentrationCutoff ((n : ℝ) + 1) 0 x ^ 2

def cylinderDifference (u v : Velocity) (t : ℝ) (x : Space) : Space := u (t,x) - v (t,x)

def localizedDifferenceEnergy (u v : Velocity) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ y, cylinderWeight n y.1 *
    dot (cylinderDifference u v t (atHeight y.1 y.2))
      (cylinderDifference u v t (atHeight y.1 y.2)) ∂cylinderMeasure

def localizedDifferenceDissipation (u v : Velocity) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ y, cylinderWeight n y.1 * ∑ j : Fin 3,
    dot (derivative (cylinderDifference u v t) j (atHeight y.1 y.2))
      (derivative (cylinderDifference u v t) j (atHeight y.1 y.2)) ∂cylinderMeasure

def localizedDifferenceInteraction (u v : Velocity) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ y, cylinderWeight n y.1 *
    dot (cylinderDifference u v t (atHeight y.1 y.2))
      (fderiv ℝ (fun x => u (t,x)) (atHeight y.1 y.2)
        (cylinderDifference u v t (atHeight y.1 y.2))) ∂cylinderMeasure

def localizedDiffusionError (u v : Velocity) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ y, scalarLaplacian (cylinderWeight n) y.1 *
    dot (cylinderDifference u v t (atHeight y.1 y.2))
      (cylinderDifference u v t (atHeight y.1 y.2)) ∂cylinderMeasure

def localizedTransportError (u v : Velocity) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ y, fderiv ℝ (cylinderWeight n) y.1
      (horizontalLinear (v (t, atHeight y.1 y.2))) *
    dot (cylinderDifference u v t (atHeight y.1 y.2))
      (cylinderDifference u v t (atHeight y.1 y.2)) ∂cylinderMeasure

def localizedPressureError (u v : Velocity) (p q : Pressure) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ y, (p (t, atHeight y.1 y.2) - q (t, atHeight y.1 y.2)) *
    fderiv ℝ (cylinderWeight n) y.1
      (horizontalLinear (cylinderDifference u v t (atHeight y.1 y.2))) ∂cylinderMeasure

def CylinderLocalEnergyIdentity : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (f u v : Velocity) (p q : Pressure),
    IsCylinderClassicalSolution ν f u p → IsCylinderClassicalSolution ν f v q →
    ∀ (n : ℕ) (t : ℝ), 0 < t →
      HasDerivAt (localizedDifferenceEnergy u v n)
        (-2 * ν * localizedDifferenceDissipation u v n t
          - 2 * localizedDifferenceInteraction u v n t
          + ν * localizedDiffusionError u v n t
          + localizedTransportError u v n t
          + 2 * localizedPressureError u v p q n t) t

end ForcedComputation.VelocityDetector

end

end OAI
