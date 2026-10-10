import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderMeasure
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Model

namespace OAI

/-! The classical comparison class on R² times the unit circle. The
Sobolev conditions use actual L2 representatives of the classical spatial
derivatives. No spatial decay of a competing solution is assumed. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set

def cylinderPullback (f : Space → ℝ) (y : Plane × ℝ) : ℝ := f (atHeight y.1 y.2)

def scalarSpatialD (j : Fin 3) (f : Space → ℝ) (x : Space) : ℝ :=
  fderiv ℝ f x (basis j)

def CylinderCInH2 (f : ℝ → Space → ℝ) (S : Set ℝ) : Prop :=
  CylinderContinuousL2 (fun t => cylinderPullback (f t)) S ∧
  (∀ j, CylinderContinuousL2 (fun t => cylinderPullback (scalarSpatialD j (f t))) S) ∧
  (∀ j k, CylinderContinuousL2
    (fun t => cylinderPullback (scalarSpatialD j (scalarSpatialD k (f t)))) S)

def CylinderCInH1 (f : ℝ → Space → ℝ) (S : Set ℝ) : Prop :=
  CylinderContinuousL2 (fun t => cylinderPullback (f t)) S ∧
  (∀ j, CylinderContinuousL2 (fun t => cylinderPullback (scalarSpatialD j (f t))) S)

def VerticallyPeriodic {A : Type*} (f : Space → A) : Prop :=
  ∀ (x : Space) (n : ℤ), f (x + (n : ℝ) • basis 2) = f x

structure IsCylinderClassicalSolution (ν : ℝ) (f u : Velocity) (p : Pressure) : Prop where
  regularity : ClassicalRegularity u p
  periodic_u : ∀ t, 0 ≤ t → VerticallyPeriodic (fun x => u (t, x))
  periodic_p : ∀ t, 0 ≤ t → VerticallyPeriodic (fun x => p (t, x))
  initial : ∀ x, u (0, x) = 0
  divergence_zero : ∀ t, 0 ≤ t → ∀ x, divergence (fun y => u (t, y)) x = 0
  equation : ∀ t, 0 ≤ t → ∀ x,
    initialTimeDerivative u t x + advection (fun y => u (t, y)) x =
      -gradient (fun y => p (t, y)) x +
        ν • laplacian (fun y => u (t, y)) x + f (t, x)
  velocity_h2 : ∀ T, 0 ≤ T → ∀ i,
    CylinderCInH2 (fun t x => u (t, x) i) (Icc 0 T)
  velocity_c1 : ∀ T, 0 ≤ T → ∀ i,
    CylinderC1L2 (fun t => cylinderPullback (fun x => u (t, x) i))
      (fun t => cylinderPullback (fun x => initialTimeDerivative u t x i)) (Icc 0 T)
  pressure_h1 : ∀ T, 0 ≤ T → CylinderCInH1 (fun t x => p (t, x)) (Icc 0 T)
  bounded : ∀ T, 0 ≤ T → ∃ B : ℝ, ∀ t ∈ Icc 0 T, ∀ x,
    ‖u (t, x)‖ + ‖fderiv ℝ (fun y => u (t, y)) x‖ ≤ B

end ForcedComputation.VelocityDetector

end

end OAI
