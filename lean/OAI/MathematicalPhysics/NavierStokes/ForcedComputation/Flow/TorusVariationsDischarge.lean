import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TorusDetectorMain
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarVariationDischarge
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatSolution

namespace OAI

/-! The torus velocity main result with both smooth-flow inputs discharged.
The scalar existence and heat-kernel inputs remain explicit. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem torus_velocity_detection_variations_discharged (hE : TorusScalarExistence) (hK : TorusHeatInput)
    (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (Ω : ℝ → ℝ → Plane → Plane)
    (hΩ : IsPlanarTransition (planarSlice (Recorder.Planar.normalizedHamiltonian I hI)) Ω)
    :
    let H := Recorder.Planar.normalizedHamiltonian I hI
    let V := planarSlice H
    let C := detectorBumpDerivativeBound
    let L := euclideanFlowBound H
    let K := PlanarHamiltonian.commonSupport (Recorder.Planar.normalizedPulse I hI) ∪
      injectionSupport
    IsCompact K ∧ K ⊆ openUnitPlane ∧
    ∃ w : ℝ → Plane → ℝ,
      ContDiff ℝ ∞ (Function.uncurry w) ∧ (∀ t x, 0 ≤ w t x) ∧
      (∀ t, 0 ≤ t → scalarMass w t ≤ (massBound L : ℝ)) ∧
      ∀ ν : ℝ, 0 < ν →
        ContDiff ℝ ∞ (detectorViscosityForce V C L ν) ∧
        SpatiallyPeriodic 1 (detectorViscosityForce V C L ν) ∧
        ContDiff ℝ ∞ (triangularVelocity (viscosityDrift ν (detectorDrift V C L))
          (viscosityScalar ν w)) ∧
        IsClassicalSolution 1 ν (detectorViscosityForce V C L ν)
          (triangularVelocity (viscosityDrift ν (detectorDrift V C L))
            (viscosityScalar ν w)) (fun _ => 0) ∧
        (∀ u p, IsClassicalSolution 1 ν (detectorViscosityForce V C L ν) u p →
          ∀ t, 0 ≤ t → ∀ x,
            u (t, x) = triangularVelocity (viscosityDrift ν (detectorDrift V C L))
              (viscosityScalar ν w) (t, x) ∧ p (t, x) = 0) ∧
        ((∃ t, 0 ≤ t ∧ ∃ x : Space, (1 / 32 : ℝ) < x 1 ∧ x 1 < 1 / 8 ∧
          1 / 2 < triangularVelocity (viscosityDrift ν (detectorDrift V C L))
            (viscosityScalar ν w) (t, x) 2) ↔ Alternating.Halts I) ∧
        (∀ t x, (∀ j, x j ∈ Icc (0 : ℝ) 1) → x ∉ K → ∀ z,
          detectorViscosityForce V C L ν (t, atHeight x z) = 0) ∧
        (∀ (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime)
          (y : SpaceTime) (ha : IsFastRealName a ν) (hb : IsFastName b y)
          (ε : ℚ) (hε : 0 < ε),
          ‖mixedDerivative (detectorViscosityForce V C L ν) α y -
            rationalVector (evaluateDetectorViscosityForce H
              (Recorder.Planar.normalizedHamiltonian_valid I hI)
              (Recorder.Planar.normalizedHamiltonian_noTime I hI)
              (Recorder.Planar.processorVelocity_joint_smooth I hI)
              C L α a b ha hb ε hε)‖ ≤ (ε : ℝ)) ∧
        (∀ (α : List (Fin 4)) (a : ℕ → ℚ) (_ha : IsFastRealName a ν)
          (T : ℚ) (y : SpaceTime), 0 ≤ y.1 → y.1 ≤ (T : ℝ) →
          ‖mixedDerivative (detectorViscosityForce V C L ν) α y‖ ≤
            (detectorViscosityBound H C L α a T : ℝ)) := by
  exact torus_velocity_detection hE hK I hI Ω hΩ
    (planarTransition_variations (Recorder.Planar.normalizedHamiltonian_valid I hI)
      (Recorder.Planar.normalizedHamiltonian_noTime I hI) hΩ)
    (planarTransition_backward_smooth (Recorder.Planar.normalizedHamiltonian_valid I hI)
      (Recorder.Planar.normalizedHamiltonian_noTime I hI) hΩ)

theorem torus_velocity_detection_scalar (hE : TorusScalarExistence)
    (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (Ω : ℝ → ℝ → Plane → Plane)
    (hΩ : IsPlanarTransition (planarSlice (Recorder.Planar.normalizedHamiltonian I hI)) Ω)
    :
    let H := Recorder.Planar.normalizedHamiltonian I hI
    let V := planarSlice H
    let C := detectorBumpDerivativeBound
    let L := euclideanFlowBound H
    let K := PlanarHamiltonian.commonSupport (Recorder.Planar.normalizedPulse I hI) ∪
      injectionSupport
    IsCompact K ∧ K ⊆ openUnitPlane ∧
    ∃ w : ℝ → Plane → ℝ,
      ContDiff ℝ ∞ (Function.uncurry w) ∧ (∀ t x, 0 ≤ w t x) ∧
      (∀ t, 0 ≤ t → scalarMass w t ≤ (massBound L : ℝ)) ∧
      ∀ ν : ℝ, 0 < ν →
        ContDiff ℝ ∞ (detectorViscosityForce V C L ν) ∧
        SpatiallyPeriodic 1 (detectorViscosityForce V C L ν) ∧
        ContDiff ℝ ∞ (triangularVelocity (viscosityDrift ν (detectorDrift V C L))
          (viscosityScalar ν w)) ∧
        IsClassicalSolution 1 ν (detectorViscosityForce V C L ν)
          (triangularVelocity (viscosityDrift ν (detectorDrift V C L))
            (viscosityScalar ν w)) (fun _ => 0) ∧
        (∀ u p, IsClassicalSolution 1 ν (detectorViscosityForce V C L ν) u p →
          ∀ t, 0 ≤ t → ∀ x,
            u (t, x) = triangularVelocity (viscosityDrift ν (detectorDrift V C L))
              (viscosityScalar ν w) (t, x) ∧ p (t, x) = 0) ∧
        ((∃ t, 0 ≤ t ∧ ∃ x : Space, (1 / 32 : ℝ) < x 1 ∧ x 1 < 1 / 8 ∧
          1 / 2 < triangularVelocity (viscosityDrift ν (detectorDrift V C L))
            (viscosityScalar ν w) (t, x) 2) ↔ Alternating.Halts I) ∧
        (∀ t x, (∀ j, x j ∈ Icc (0 : ℝ) 1) → x ∉ K → ∀ z,
          detectorViscosityForce V C L ν (t, atHeight x z) = 0) ∧
        (∀ (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime)
          (y : SpaceTime) (ha : IsFastRealName a ν) (hb : IsFastName b y)
          (ε : ℚ) (hε : 0 < ε),
          ‖mixedDerivative (detectorViscosityForce V C L ν) α y -
            rationalVector (evaluateDetectorViscosityForce H
              (Recorder.Planar.normalizedHamiltonian_valid I hI)
              (Recorder.Planar.normalizedHamiltonian_noTime I hI)
              (Recorder.Planar.processorVelocity_joint_smooth I hI)
              C L α a b ha hb ε hε)‖ ≤ (ε : ℝ)) ∧
        (∀ (α : List (Fin 4)) (a : ℕ → ℚ) (_ha : IsFastRealName a ν)
          (T : ℚ) (y : SpaceTime), 0 ≤ y.1 → y.1 ≤ (T : ℝ) →
          ‖mixedDerivative (detectorViscosityForce V C L ν) α y‖ ≤
            (detectorViscosityBound H C L α a T : ℝ)) := by
  exact torus_velocity_detection_variations_discharged hE torusHeatInput I hI Ω hΩ

end ForcedComputation.VelocityDetector

end

end OAI
