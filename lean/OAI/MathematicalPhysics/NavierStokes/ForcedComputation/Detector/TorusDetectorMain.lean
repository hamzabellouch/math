import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorViscosityObservation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorViscosityProgram
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorProcessorSupport

namespace OAI

/-! The compact-chart velocity detector on the unit three-torus. All
analytic existence inputs are explicit. The force is given by finite
expressions and terminating rational arithmetic, before solving the fluid. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem triangularVelocity_vertical (a : ℝ → Plane → Plane) (w : ℝ → Plane → ℝ)
    (y : SpaceTime) : triangularVelocity a w y 2 = w y.1 (horizontal y.2) := by
  rw [triangularVelocity, triangularLift_eq]
  rfl

theorem triangularVelocity_fixed_observation (a : ℝ → Plane → Plane) (w : ℝ → Plane → ℝ) :
    (∃ t, 0 ≤ t ∧ ∃ x : Space, (1 / 32 : ℝ) < x 1 ∧ x 1 < 1 / 8 ∧
      1 / 2 < triangularVelocity a w (t, x) 2) ↔
      ∃ t, 0 ≤ t ∧ ∃ x ∈ Recorder.Planar.observer, 1 / 2 < w t x := by
  simp only [triangularVelocity_vertical]
  constructor
  · rintro ⟨t, ht, x, hx₁, hx₂, hv⟩
    exact ⟨t, ht, horizontal x, ⟨hx₁, hx₂⟩, hv⟩
  · rintro ⟨t, ht, x, hx, hv⟩
    refine ⟨t, ht, atHeight x 0, hx.1, hx.2, ?_⟩
    simpa only [atHeight_horizontal] using hv

attribute [local irreducible] Recorder.Planar.normalizedHamiltonian planarSlice
  euclideanFlowBound detectorDrift detectorSource

theorem torus_velocity_detection (hE : TorusScalarExistence) (hK : TorusHeatInput)
    (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (Ω : ℝ → ℝ → Plane → Plane)
    (hΩ : IsPlanarTransition (planarSlice (Recorder.Planar.normalizedHamiltonian I hI)) Ω)
    (hv : PlanarVariations (planarSlice (Recorder.Planar.normalizedHamiltonian I hI)) Ω)
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ω y.1 (-y.1) y.2)) :
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
  dsimp only
  obtain ⟨Ψ, hP⟩ := Recorder.Planar.smooth_planar_processor I hI Ω hΩ hv
  obtain ⟨hcompact, hinside, hsupp⟩ := processor_detector_force_support I hI hP
    detectorBumpDerivativeBound (euclideanFlowBound (Recorder.Planar.normalizedHamiltonian I hI))
  refine ⟨hcompact, hinside, ?_⟩
  obtain ⟨w, hw, hn, hm, hνs⟩ := processor_detector_all_viscosities hE hK I hI hP hv hback
  refine ⟨w, hw, hn, hm, ?_⟩
  intro ν hν
  obtain ⟨hu, huniq, hobs⟩ := hνs ν hν
  have hvs := viscosityDrift_smooth
    (detectorDrift_smooth hP.torus_smooth detectorBumpDerivativeBound
      (euclideanFlowBound (Recorder.Planar.normalizedHamiltonian I hI))) ν
  have hhs := viscositySource_smooth
    (detectorSource_smooth detectorBumpDerivativeBound
      (euclideanFlowBound (Recorder.Planar.normalizedHamiltonian I hI))) ν
  refine ⟨triangularForce_smooth hvs hhs ν,
    triangularForce_periodic hvs
      (viscosityDrift_periodic (detectorDrift_periodic hP.torus_spatial_periodic _ _) ν)
      (viscositySource_periodic (detectorSource_periodic _ _) ν) ν,
    triangularVelocity_smooth hvs (viscosityScalar_smooth hw ν),
    hu, huniq, (triangularVelocity_fixed_observation _ _).trans hobs, ?_, ?_, ?_⟩
  · intro t x hx hxK z
    rw [detectorViscosityForce_eq _ hP.torus_smooth]
    change forceViscosityLinear ν (detectorForce _ _ _ (ν * t, atHeight x z)) = 0
    rw [hsupp (ν * t) x hx hxK z, map_zero]
  · intro α a b y ha hb ε hε
    exact evaluateDetectorViscosityForce_spec hP.expression_valid hP.expression_noTime
      hP.torus_smooth _ _ α a b ha hb ε hε
  · intro α a ha T y ht hT
    exact detectorViscosityBound_spec hν hP.expression_valid hP.expression_noTime
      hP.torus_smooth _ _ α ha T ht hT

end ForcedComputation.VelocityDetector

end

end OAI
