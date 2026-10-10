import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFilteredLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingEvaluation

namespace OAI

/-! # Scalar multiplication and pointwise bounds for physical ball observations -/

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingPhysicalBall_smul (a k L R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (c : ℝ) (f : FourierL2) :
    expandingPhysicalBall a k L R ha ha1 hk hL (c • f) =
      c • expandingPhysicalBall a k L R ha ha1 hk hL f := by
  ext y
  simp only [expandingPhysicalBall_apply, ContinuousMap.smul_apply]
  rw [expandingTorusFunction_eq_evaluation a k L ha ha1 hk hL,
    expandingTorusFunction_eq_evaluation a k L ha ha1 hk hL]
  exact ((expandingPointEvaluation a k L ha ha1 hk hL _).restrictScalars ℝ).map_smul c f

theorem expandingPhysicalBall_point_le (a k L R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (f : FourierL2) (y : E) (hy : ‖y‖ ≤ R) :
    ‖expandingTorusFunction a k L f (euclideanToTorus (L⁻¹ • y))‖ ≤
      ‖expandingPhysicalBall a k L R ha ha1 hk hL f‖ := by
  let x : Metric.closedBall (0 : E) R := ⟨y, by simpa using hy⟩
  simpa only [expandingPhysicalBall_apply] using
    ContinuousMap.norm_coe_le_norm (expandingPhysicalBall a k L R ha ha1 hk hL f) x

end DefocusingNLS

end OAI
