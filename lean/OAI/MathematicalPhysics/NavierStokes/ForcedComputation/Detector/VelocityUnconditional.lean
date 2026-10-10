import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarDischarge
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusScalarDischarge
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.TorusVariationsDischarge
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.VelocityDecisionDischarge
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.ProcessorFlowSmooth

namespace OAI

/-! The velocity-detection main results with the scalar existence inputs discharged. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem torus_velocity_detection_unconditional
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
  exact torus_velocity_detection_scalar torusScalarExistence I hI Ω hΩ

theorem torus_velocity_undecidable_unconditional {ν : ℝ} (hν : 0 < ν) :
    NoCompiledInputDecider (fun I hI =>
      TorusVelocityEvent ν (compiledTorusDetectorForce ν I hI)) :=
  torus_velocity_undecidable_scalar torusScalarExistence hν

theorem plane_velocity_undecidable_unconditional :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (ν : ℝ), 0 < ν → ∀ (a : ℕ → ℚ), IsFastRealName a ν →
      NoCompiledInputDecider (fun I hI =>
        PlaneVelocityEvent ν (ExpandingDetector.compiledExpandingForce C I hI a ν)) :=
  plane_velocity_undecidable_scalar planeScalarExistence

end ForcedComputation.VelocityDetector

namespace ForcedComputation.ExpandingDetector
open ShearFlows Set VelocityDetector
open scoped ContDiff

theorem whole_plane_velocity_detection_unconditional :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
      (ν : ℝ), 0 < ν → ∀ (a : ℕ → ℚ), IsFastRealName a ν →
      let f := compiledExpandingForce C I hI a ν
      ContDiff ℝ ∞ f ∧
      (∀ α : List (Fin 4), ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖mixedDerivative f α y‖ ≤ B) ∧
      (∀ T : ℝ, ∃ K : Set Plane, IsCompact K ∧
        ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space, horizontalLinear x ∉ K → f (t,x) = 0) ∧
      (∀ (α : List (Fin 4)) (b : ℕ → RationalSpaceTime) (y : SpaceTime),
        IsFastName b y → ∀ (ε : ℚ) (hε : 0 < ε),
          ‖mixedDerivative f α y -
            rationalVector (evaluateCompiledExpandingForce C I hI a α b ε hε)‖ ≤ (ε : ℝ)) ∧
      (∀ (α : List (Fin 4)) (R : ℚ) (y : SpaceTime),
        (∀ j, |timeSpaceCoord j y| ≤ |(R : ℝ)|) →
        ‖mixedDerivative f α y‖ ≤ (compiledExpandingForceBound C I hI a α R : ℝ)) ∧
      WholePlaneDetection ν f I :=
  whole_plane_velocity_detection planeScalarExistence cylinder_local_energy_identity

end ForcedComputation.ExpandingDetector

namespace ForcedComputation.VelocityDetector.CompactCenter
open ShearFlows Set
open scoped ContDiff

theorem compact_detector_unconditional
    {V : ℝ → Plane → Plane} (hV : ProcessorInput V)
    (Ψ : ℝ → ℝ → Plane → Plane) (hΨ : IsPlanarTransition V Ψ)
    (L : ℕ) (hL : 0 < L)
    (h₁ : ∀ s x, ‖fderiv ℝ (euclideanMap (V s)) x‖ ≤ (L : ℝ))
    (h₂ : ∀ s x, ‖fderiv ℝ (fderiv ℝ (euclideanMap (V s))) x‖ ≤ (L : ℝ))
    (p : Plane) (b : ℕ → RationalSpaceTime)
    (hb : IsFastName b (shiftSpaceTime (centerShift p))) :
    let C := detectorBumpDerivativeBound
    let K := processorSupport V ∪ injectionNeighborhood p
    IsClosed K ∧ p ∈ injectionNeighborhood p ∧
    ∃ w : ℝ → Plane → ℝ,
      ContDiff ℝ ∞ (Function.uncurry w) ∧ (∀ t x, 0 ≤ w t x) ∧
      (∀ t, 0 ≤ t → scalarMass w t ≤ (massBound L : ℝ)) ∧
      (massBound L : ℝ) < 1 / 100000000000 ∧
      ∀ ν : ℝ, 0 < ν →
        let u := triangularVelocity (viscosityDrift ν (centeredDrift V p C L)) (viscosityScalar ν w)
        ContDiff ℝ ∞ (centeredForce V p C L ν) ∧ SpatiallyPeriodic 1 (centeredForce V p C L ν) ∧
        ContDiff ℝ ∞ u ∧ IsClassicalSolution 1 ν (centeredForce V p C L ν) u (fun _ => 0) ∧
        (∀ u' q, IsClassicalSolution 1 ν (centeredForce V p C L ν) u' q →
          ∀ t, 0 ≤ t → ∀ x, u' (t, x) = u (t, x) ∧ q (t, x) = 0) ∧
        (∀ t x z, 0 ≤ u (t, atHeight x z) 2) ∧
        (∀ (E : Set Plane) (_hopen : IsOpen E) (d H : ℝ), DetectorPair d H →
          ((∃ k : ℕ, Ψ 0 k p ∈ E) →
            ∃ t, 0 ≤ t ∧ ∃ x ∈ E, ∀ z, 1 / 2 < u (t, atHeight x z) 2) ∧
          ((∀ s, 0 ≤ s → ∀ x ∈ E, 2 * d ≤ torusNorm (Ψ 0 s p - x)) →
            ∀ t, 0 ≤ t → ∀ x ∈ E, ∀ z, u (t, atHeight x z) 2 < 1 / 2)) ∧
        (∀ t x, x ∉ K → ∀ z, centeredForce V p C L ν (t, atHeight x z) = 0) ∧
        (∀ (α : List (Fin 4)) (a : ℕ → ℚ) (c : ℕ → RationalSpaceTime)
          (y : SpaceTime) (ha : IsFastRealName a ν) (hc : IsFastName c y)
          (ε : ℚ) (hε : 0 < ε),
          ‖mixedDerivative (centeredForce V p C L ν) α y -
            rationalVector (evaluateCenteredForce hV.smooth hV.oracle p b hb C L
              α a c ha hc ε hε)‖ ≤ (ε : ℝ)) ∧
        (∀ (α : List (Fin 4)) (a : ℕ → ℚ) (_ha : IsFastRealName a ν)
          (T : ℚ) (y : SpaceTime), 0 ≤ y.1 → y.1 ≤ (T : ℝ) →
          ‖mixedDerivative (centeredForce V p C L ν) α y‖ ≤
            (centeredForceBound hV.smooth hV.oracle p b hb C L α a T : ℝ)) := by
  exact compact_detector torusScalarExistence torusHeatInput hV Ψ hΨ
    (hV.variations hΨ) (hV.backward_smooth hΨ) L hL h₁ h₂ p b hb

end ForcedComputation.VelocityDetector.CompactCenter

end

end OAI
