import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.StationaryProgram
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.StationaryObservation

namespace OAI

/-! The main theorem of Universal Computation with Eventually Stationary
Navier–Stokes Forcing, including a terminating finite force evaluator,
global derivative bounds, and the fixed-particle observation. -/

namespace ForcedComputation
open ShearFlows Recorder.Planar

theorem stationary_effective_computation (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (ν : ℝ) (hν : 0 < ν) :
    StationaryFluidProperties 1 ν (stationaryVelocity I hI) ∧
    (∀ (α : List (Fin 4)) (b : ℕ → RationalSpaceTime) (y : SpaceTime)
      (_hb : IsFastName b y) (ε : ℚ) (hε : 0 < ε),
      ‖mixedDerivative (stationaryVelocity I hI) α y -
        rationalVector (evaluateStartupVelocity (stationaryCode I hI)
          (stationaryCode_valid I hI) α b ε hε)‖ ≤ (ε : ℝ)) ∧
    (∀ (α : List (Fin 4)) (a : ℕ → ℚ) (_ha : IsFastRealName a ν)
      (b : ℕ → RationalSpaceTime) (y : SpaceTime) (_hb : IsFastName b y)
      (ε : ℚ) (hε : 0 < ε),
      ‖mixedDerivative (stationaryForce ν I hI) α y -
        rationalVector (evaluateStartupForce (stationaryCode I hI)
          (stationaryCode_valid I hI) α a b ε hε)‖ ≤ (ε : ℝ)) ∧
    (∀ (α : List (Fin 4)) (y : SpaceTime),
      ‖mixedDerivative (stationaryVelocity I hI) α y‖ ≤
        (startupVelocityBound (stationaryCode I hI) α : ℝ)) ∧
    (∀ (α : List (Fin 4)) (a : ℕ → ℚ) (_ha : IsFastRealName a ν) (y : SpaceTime),
      ‖mixedDerivative (stationaryForce ν I hI) α y‖ ≤
        (startupForceBound (stationaryCode I hI) α a : ℝ)) ∧
    ∃ Φ : ℝ → Space → Space, IsMaterialFlow 1 (stationaryVelocity I hI) Φ ∧
      (Reaches (fun t => Φ t stationaryStartingPoint) stationaryObserver ↔ Alternating.Halts I) := by
  refine ⟨stationary_program_properties I hI ν hν.le,
    stationary_velocity_evaluate I hI, stationary_force_evaluate I hI ν,
    stationary_velocity_bound I hI, stationary_force_bound I hI ν, ?_⟩
  obtain ⟨Φ, hΦ, hstartup, he⟩ := stationary_program_flows I hI
  refine ⟨fun t x => Φ (accumulatedClock startupRamp t) x, hstartup, ?_⟩
  exact (he stationaryStartingPoint stationaryObserver).trans
    (stationary_suspension_observation I hI hΦ)

end ForcedComputation

end OAI
