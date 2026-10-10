import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.VelocityDecisionCorollaries
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FiniteMachineHaltingDischarge
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderEnergyIdentity
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarVariationDischarge
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatSolution

namespace OAI

/-! The velocity-decision main results with machine undecidability, smooth
flow dependence and localized energy identity discharged. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set

theorem torus_velocity_undecidable_parabolic
    (hE : TorusScalarExistence) (hK : TorusHeatInput) {ν : ℝ} (hν : 0 < ν) :
    NoCompiledInputDecider (fun I hI =>
      TorusVelocityEvent ν (compiledTorusDetectorForce ν I hI)) := by
  apply torus_velocity_undecidable finiteMachineHaltingUndecidable hE hK
  · intro I hI Ω hΩ
    exact planarTransition_variations (Recorder.Planar.normalizedHamiltonian_valid I hI)
      (Recorder.Planar.normalizedHamiltonian_noTime I hI) hΩ
  · intro I hI Ω hΩ
    exact planarTransition_backward_smooth (Recorder.Planar.normalizedHamiltonian_valid I hI)
      (Recorder.Planar.normalizedHamiltonian_noTime I hI) hΩ
  · exact hν

/-- Only the scalar advection-diffusion existence input remains. -/
theorem torus_velocity_undecidable_scalar
    (hE : TorusScalarExistence) {ν : ℝ} (hν : 0 < ν) :
    NoCompiledInputDecider (fun I hI =>
      TorusVelocityEvent ν (compiledTorusDetectorForce ν I hI)) :=
  torus_velocity_undecidable_parabolic hE torusHeatInput hν

theorem plane_velocity_undecidable_scalar (hE : PlaneScalarExistence) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (ν : ℝ), 0 < ν → ∀ (a : ℕ → ℚ), IsFastRealName a ν →
      NoCompiledInputDecider (fun I hI =>
        PlaneVelocityEvent ν (ExpandingDetector.compiledExpandingForce C I hI a ν)) :=
  plane_velocity_undecidable finiteMachineHaltingUndecidable hE cylinder_local_energy_identity

end ForcedComputation.VelocityDetector

end

end OAI
