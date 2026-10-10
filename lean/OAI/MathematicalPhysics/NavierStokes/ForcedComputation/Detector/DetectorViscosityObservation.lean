import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorProcessorObservation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorViscosity

namespace OAI

/-! One scalar construction gives the halting observation and unique
classical fluid at every positive viscosity. The force is prescribed from
the processor and source, before the scalar solution is chosen. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows
open scoped ContDiff

attribute [local irreducible] Recorder.Planar.normalizedHamiltonian planarSlice
  euclideanFlowBound detectorDrift detectorSource

theorem processor_detector_all_viscosities (hE : TorusScalarExistence)
    (hK : TorusHeatInput) (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    {Ω Ψ : ℝ → ℝ → Plane → Plane}
    (hP : Recorder.Planar.ProcessorProperties I hI Ω Ψ)
    (hv : PlanarVariations (planarSlice (Recorder.Planar.normalizedHamiltonian I hI)) Ω)
    (hback : ContDiff ℝ ∞ (fun y : ℝ × Plane => Ω y.1 (-y.1) y.2)) :
    let V := planarSlice (Recorder.Planar.normalizedHamiltonian I hI)
    let L := euclideanFlowBound (Recorder.Planar.normalizedHamiltonian I hI)
    ∃ w : ℝ → Plane → ℝ,
      ContDiff ℝ ∞ (Function.uncurry w) ∧ (∀ t x, 0 ≤ w t x) ∧
      (∀ t, 0 ≤ t → scalarMass w t ≤ (massBound L : ℝ)) ∧
      ∀ ν : ℝ, 0 < ν →
        IsClassicalSolution 1 ν (detectorViscosityForce V detectorBumpDerivativeBound L ν)
          (triangularVelocity (viscosityDrift ν (detectorDrift V detectorBumpDerivativeBound L))
            (viscosityScalar ν w)) (fun _ => 0) ∧
        (∀ u p, IsClassicalSolution 1 ν
            (detectorViscosityForce V detectorBumpDerivativeBound L ν) u p →
          ∀ t, 0 ≤ t → ∀ x, u (t, x) =
            triangularVelocity (viscosityDrift ν (detectorDrift V detectorBumpDerivativeBound L))
              (viscosityScalar ν w) (t, x) ∧ p (t, x) = 0) ∧
        ((∃ t, 0 ≤ t ∧ ∃ x ∈ Recorder.Planar.observer,
          1 / 2 < viscosityScalar ν w t x) ↔ Alternating.Halts I) := by
  dsimp only
  let V := planarSlice (Recorder.Planar.normalizedHamiltonian I hI)
  let L := euclideanFlowBound (Recorder.Planar.normalizedHamiltonian I hI)
  have hV : ContDiff ℝ ∞ (Function.uncurry V) := hP.torus_smooth
  obtain ⟨w, hs, hw, hwp, hn, _⟩ := detectorScalar_exists (V := V) hE
    hV hP.torus_spatial_periodic detectorBumpDerivativeBound L
  refine ⟨w, hw, hn, ?_, ?_⟩
  · intro t ht
    exact detector_scalar_mass_bound (V := V) hV hP.torus_spatial_periodic
      hP.torus_solenoidal detectorBumpDerivativeBound L hs hw ht
  · intro ν hν
    have hu := detectorViscosity_solution (V := V) hV hP.torus_spatial_periodic
      hP.torus_solenoidal detectorBumpDerivativeBound L hs hw hwp hν
    refine ⟨hu, finite_time_classical_unique (by norm_num) hν.le hu, ?_⟩
    rw [viscosityScalar_observation hν]
    exact detector_processor_observation hK I hI hP hv hback hs hw

end ForcedComputation.VelocityDetector

end

end OAI
