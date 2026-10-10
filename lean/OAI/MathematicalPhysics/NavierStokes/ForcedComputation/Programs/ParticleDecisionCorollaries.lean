import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ParticleEvents

namespace OAI

/-! Undecidability of the compiled particle experiments, conditional only on
the separately cited finite-machine halting input. -/

namespace ForcedComputation
open ShearFlows

/-- 379-01, the undecidability corollary for the initialized experiment. -/
theorem initialized_particle_undecidable (hT : FiniteMachineHaltingUndecidable)
    {ν : ℝ} (hν : 0 < ν) :
    NoCompiledInputDecider (fun I hI =>
      MaterialEvent (machineVelocity I hI) ![1 / 8, 3 / 8, 1 / 2] particleRightHalf) :=
  noCompiledInputDecider_of_halting hT (fun I hI => initialized_material_event_iff I hI hν)

/-- 379-02, the fixed-particle undecidability corollary. -/
theorem fixed_particle_undecidable (hT : FiniteMachineHaltingUndecidable)
    {ν : ℝ} (hν : 0 < ν) :
    NoCompiledInputDecider (fun I hI =>
      MaterialEvent (fixedParticleVelocity I hI) ![1 / 8, 3 / 8, 0] particleRightHalf) :=
  noCompiledInputDecider_of_halting hT (fun I hI => fixed_particle_material_event_iff I hI hν)

/-- 379-03, eventual stationarity does not make the particle event decidable. -/
theorem stationary_particle_undecidable (hT : FiniteMachineHaltingUndecidable)
    {ν : ℝ} (hν : 0 < ν) :
    NoCompiledInputDecider (fun I hI =>
      MaterialEvent (stationaryVelocity I hI) stationaryStartingPoint
        stationaryObserver) :=
  noCompiledInputDecider_of_halting hT (fun I hI => stationary_material_event_iff I hI hν)

/-- 379-08, the logarithmic-clock particle event remains undecidable. -/
theorem slow_particle_undecidable (hT : FiniteMachineHaltingUndecidable)
    {ν : ℝ} (hν : 0 < ν) :
    NoCompiledInputDecider (fun I hI =>
      MaterialEvent (torusSlowVelocity I hI) ![1 / 4, 1 / 2, 1 / 2] particleRightHalf) :=
  noCompiledInputDecider_of_halting hT (fun I hI => slow_material_event_iff I hI hν)

/-- The interspersed-history prefix experiment has no total decision algorithm. -/
theorem prefix_particle_undecidable (hT : FiniteMachineHaltingUndecidable)
    {ν : ℝ} (hν : 0 < ν) :
    NoCompiledInputDecider (fun I hI =>
      MaterialEvent (prefixVelocity I hI) ![1 / 8, 1 / 4, 1 / 4] particleRightHalf) :=
  noCompiledInputDecider_of_halting hT (fun I hI => prefix_material_event_iff I hI hν)

/-- Repeating the initializer does not make the material observation decidable. -/
theorem periodic_particle_undecidable (hT : FiniteMachineHaltingUndecidable)
    {ν : ℝ} (hν : 0 < ν) :
    NoCompiledInputDecider (fun I hI =>
      MaterialEvent (periodicVelocity I hI) ![1 / 4, 1 / 2, 1 / 4]
        {x | 1 / 2 < x 0 ∧ x 0 < 7 / 8}) :=
  noCompiledInputDecider_of_halting hT (fun I hI => periodic_material_event_iff I hI hν)

end ForcedComputation

end OAI
