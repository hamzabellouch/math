import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NormalizedPlanarProgram
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.HamiltonianStartup

namespace OAI

/-! A finite force program for eventually stationary computation, with
analytic properties and terminating derivative evaluation. -/

namespace ForcedComputation
open ShearFlows Recorder.Planar

def stationaryCode (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    VelocityExpr := SpatialExpression.suspensionCode (normalizedHamiltonian I hI)

theorem stationaryCode_valid (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    (stationaryCode I hI).Valid :=
  SpatialExpression.suspensionCode_valid (normalizedHamiltonian_valid I hI)

noncomputable def stationaryVelocity (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : Velocity :=
  hamiltonianStartupVelocity (normalizedHamiltonian I hI)

noncomputable def stationaryForce (ν : ℝ) (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) : Velocity := residual ν (stationaryVelocity I hI)

theorem stationary_program_properties (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (ν : ℝ) (hν : 0 ≤ ν) :
    StationaryFluidProperties 1 ν (stationaryVelocity I hI) :=
  (hamiltonian_startup_effective (normalizedHamiltonian_valid I hI)
    (normalizedHamiltonian_noTime I hI) (normalizedHamiltonian_periodic I hI) hν).1

theorem stationary_velocity_evaluate (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (α : List (Fin 4)) (b : ℕ → RationalSpaceTime)
    (y : SpaceTime) (hb : IsFastName b y) (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (stationaryVelocity I hI) α y -
      rationalVector (evaluateStartupVelocity (stationaryCode I hI)
        (stationaryCode_valid I hI) α b ε hε)‖ ≤ (ε : ℝ) :=
  evaluateStartupVelocity_spec (stationaryCode_valid I hI)
    (SpatialExpression.suspensionCode_val (normalizedHamiltonian_valid I hI)
      (normalizedHamiltonian_noTime I hI)) α hb ε hε

theorem stationary_force_evaluate (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (ν : ℝ) (α : List (Fin 4))
    (a : ℕ → ℚ) (ha : IsFastRealName a ν) (b : ℕ → RationalSpaceTime)
    (y : SpaceTime) (hb : IsFastName b y) (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (stationaryForce ν I hI) α y -
      rationalVector (evaluateStartupForce (stationaryCode I hI)
        (stationaryCode_valid I hI) α a b ε hε)‖ ≤ (ε : ℝ) :=
  evaluateStartupForce_spec (stationaryCode_valid I hI)
    (SpatialExpression.suspensionCode_val (normalizedHamiltonian_valid I hI)
      (normalizedHamiltonian_noTime I hI)) α ha hb ε hε

theorem stationary_velocity_bound (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (α : List (Fin 4)) (y : SpaceTime) :
    ‖mixedDerivative (stationaryVelocity I hI) α y‖ ≤
      (startupVelocityBound (stationaryCode I hI) α : ℝ) :=
  startupVelocityBound_spec (stationaryCode_valid I hI)
    (SpatialExpression.suspensionCode_val (normalizedHamiltonian_valid I hI)
      (normalizedHamiltonian_noTime I hI)) α y

theorem stationary_force_bound (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (ν : ℝ) (α : List (Fin 4))
    (a : ℕ → ℚ) (ha : IsFastRealName a ν) (y : SpaceTime) :
    ‖mixedDerivative (stationaryForce ν I hI) α y‖ ≤
      (startupForceBound (stationaryCode I hI) α a : ℝ) :=
  startupForceBound_spec (stationaryCode_valid I hI)
    (SpatialExpression.suspensionCode_val (normalizedHamiltonian_valid I hI)
      (normalizedHamiltonian_noTime I hI)) α ha y

theorem stationary_program_flows (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    ∃ Φ : ℝ → Space → Space,
      IsMaterialFlow 1 (fun y =>
        SpatialExpression.suspensionField (normalizedHamiltonian I hI) y.2) Φ ∧
      IsMaterialFlow 1 (stationaryVelocity I hI)
        (fun t x => Φ (accumulatedClock startupRamp t) x) ∧
      ∀ x O, Reaches (fun t => Φ (accumulatedClock startupRamp t) x) O ↔
        Reaches (fun t => Φ t x) O :=
  startup_materialFlow (by norm_num)
    (SpatialExpression.suspensionField_smooth (normalizedHamiltonian_valid I hI))
    (SpatialExpression.suspensionField_periodic (normalizedHamiltonian_valid I hI)
      (normalizedHamiltonian_periodic I hI))

end ForcedComputation

end OAI
