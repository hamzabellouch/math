import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.StationaryBundle
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.StartupEffective
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.SuspensionExpressions

namespace OAI

/-! Assembly of the analytic and effective parts of the eventually stationary
construction from its finite scalar Hamiltonian. -/

namespace ForcedComputation
open ShearFlows

noncomputable def hamiltonianStartupVelocity (H : FieldExpr) : Velocity :=
  rampVelocity startupRamp (SpatialExpression.suspensionField H)

theorem hamiltonian_startup_effective {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H)
    (hP : CubePeriodic 1 (SpatialExpression.spatialValue H))
    {ν : ℝ} (hν : 0 ≤ ν) :
    StationaryFluidProperties 1 ν (hamiltonianStartupVelocity H) ∧
    (∀ (α : List (Fin 4)) (b : ℕ → RationalSpaceTime) (y : SpaceTime),
      IsFastName b y → ∀ (ε : ℚ) (hε : 0 < ε),
        ‖mixedDerivative (hamiltonianStartupVelocity H) α y -
          rationalVector (evaluateStartupVelocity (SpatialExpression.suspensionCode H)
            (SpatialExpression.suspensionCode_valid hH) α b ε hε)‖ ≤ (ε : ℝ)) ∧
    (∀ (α : List (Fin 4)) (a : ℕ → ℚ), IsFastRealName a ν →
      ∀ (b : ℕ → RationalSpaceTime) (y : SpaceTime), IsFastName b y →
        ∀ (ε : ℚ) (hε : 0 < ε),
          ‖mixedDerivative (residual ν (hamiltonianStartupVelocity H)) α y -
            rationalVector (evaluateStartupForce (SpatialExpression.suspensionCode H)
              (SpatialExpression.suspensionCode_valid hH) α a b ε hε)‖ ≤ (ε : ℝ)) ∧
    (∀ (α : List (Fin 4)) (y : SpaceTime),
      ‖mixedDerivative (hamiltonianStartupVelocity H) α y‖ ≤
        (startupVelocityBound (SpatialExpression.suspensionCode H) α : ℝ)) ∧
    (∀ (α : List (Fin 4)) (a : ℕ → ℚ), IsFastRealName a ν → ∀ y,
      ‖mixedDerivative (residual ν (hamiltonianStartupVelocity H)) α y‖ ≤
        (startupForceBound (SpatialExpression.suspensionCode H) α a : ℝ)) ∧
    ∃ Φ : ℝ → Space → Space,
      IsMaterialFlow 1 (fun y => SpatialExpression.suspensionField H y.2) Φ ∧
      IsMaterialFlow 1 (hamiltonianStartupVelocity H)
        (fun t x => Φ (accumulatedClock startupRamp t) x) ∧
      ∀ x O, Reaches (fun t => Φ (accumulatedClock startupRamp t) x) O ↔
        Reaches (fun t => Φ t x) O := by
  have hs := SpatialExpression.suspensionField_smooth hH
  have hp := SpatialExpression.suspensionField_periodic hH hP
  have hd := SpatialExpression.suspensionField_divergence hH
  have hm := SpatialExpression.suspensionField_mean_zero hH hP
  have hc := SpatialExpression.suspensionCode_valid hH
  have hv := SpatialExpression.suspensionCode_val hH hT
  refine ⟨startup_bundle (by norm_num) hν hs hp hd hm, ?_, ?_, ?_, ?_,
    startup_materialFlow (by norm_num) hs hp⟩
  · intro α b y hb ε hε
    exact evaluateStartupVelocity_spec hc hv α hb ε hε
  · intro α a ha b y hb ε hε
    exact evaluateStartupForce_spec hc hv α ha hb ε hε
  · intro α y
    exact startupVelocityBound_spec hc hv α y
  · intro α a ha y
    exact startupForceBound_spec hc hv α ha y

end ForcedComputation

end OAI
