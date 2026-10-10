import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ParticleDecisionCorollaries
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FiniteMachineHaltingDischarge

namespace OAI

/-! Particle-decision main results with the finite-machine input discharged. -/

namespace ForcedComputation
open ShearFlows

theorem initialized_particle_undecidable_unconditional
    {ν : ℝ} (hν : 0 < ν) :
    NoCompiledInputDecider (fun I hI =>
      MaterialEvent (machineVelocity I hI) ![1 / 8, 3 / 8, 1 / 2] particleRightHalf) :=
  initialized_particle_undecidable finiteMachineHaltingUndecidable hν

theorem fixed_particle_undecidable_unconditional
    {ν : ℝ} (hν : 0 < ν) :
    NoCompiledInputDecider (fun I hI =>
      MaterialEvent (fixedParticleVelocity I hI) ![1 / 8, 3 / 8, 0] particleRightHalf) :=
  fixed_particle_undecidable finiteMachineHaltingUndecidable hν

theorem stationary_particle_undecidable_unconditional
    {ν : ℝ} (hν : 0 < ν) :
    NoCompiledInputDecider (fun I hI =>
      MaterialEvent (stationaryVelocity I hI) stationaryStartingPoint
        stationaryObserver) :=
  stationary_particle_undecidable finiteMachineHaltingUndecidable hν

theorem slow_particle_undecidable_unconditional
    {ν : ℝ} (hν : 0 < ν) :
    NoCompiledInputDecider (fun I hI =>
      MaterialEvent (torusSlowVelocity I hI) ![1 / 4, 1 / 2, 1 / 2] particleRightHalf) :=
  slow_particle_undecidable finiteMachineHaltingUndecidable hν

theorem prefix_particle_undecidable_unconditional
    {ν : ℝ} (hν : 0 < ν) :
    NoCompiledInputDecider (fun I hI =>
      MaterialEvent (prefixVelocity I hI) ![1 / 8, 1 / 4, 1 / 4] particleRightHalf) :=
  prefix_particle_undecidable finiteMachineHaltingUndecidable hν

theorem periodic_particle_undecidable_unconditional
    {ν : ℝ} (hν : 0 < ν) :
    NoCompiledInputDecider (fun I hI =>
      MaterialEvent (periodicVelocity I hI) ![1 / 4, 1 / 2, 1 / 4]
        {x | 1 / 2 < x 0 ∧ x 0 < 7 / 8}) :=
  periodic_particle_undecidable finiteMachineHaltingUndecidable hν

end ForcedComputation

end OAI
