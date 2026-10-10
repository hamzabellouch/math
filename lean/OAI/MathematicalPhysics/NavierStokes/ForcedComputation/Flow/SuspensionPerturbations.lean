import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarSuspensionBridge
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.EffectiveInterface

namespace OAI

/-! An explicit integer Lipschitz bound for the finite suspension formula and
the resulting quantitative stability of its actual material trajectories. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set
open scoped NNReal

def suspensionLipschitzBound (H : FieldExpr) : ℕ :=
  (SpatialExpression.suspensionCode H).modulusBound []

theorem suspensionField_lipschitz {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) :
    LipschitzWith (suspensionLipschitzBound H : ℝ≥0)
      (SpatialExpression.suspensionField H) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hb := VelocityExpr.lipschitz_bound (SpatialExpression.suspensionCode_valid hH)
    [] (0, x) (0, y)
  rw [SpatialExpression.suspensionCode_val hH hT] at hb
  simpa only [mixedDerivative, suspensionLipschitzBound, Prod.mk_sub_mk, sub_self,
    Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _), dist_eq_norm,
    NNReal.coe_natCast] using hb

theorem suspension_flow_perturbation {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (fun y => SpatialExpression.suspensionField H y.2) Φ)
    (x y : Space) {a t : ℝ} (hat : a ≤ t) :
    dist (Φ t x) (Φ t y) ≤ dist (Φ a x) (Φ a y) *
      Real.exp ((suspensionLipschitzBound H : ℝ) * (t - a)) := by
  have hx : Continuous (fun s => Φ s x) :=
    continuous_iff_continuousAt.mpr (fun s => (hΦ.ode s x).continuousAt)
  have hy : Continuous (fun s => Φ s y) :=
    continuous_iff_continuousAt.mpr (fun s => (hΦ.ode s y).continuousAt)
  exact dist_le_of_trajectories_ODE (fun _ => suspensionField_lipschitz hH hT)
    hx.continuousOn (fun s _ => (hΦ.ode s x).hasDerivWithinAt)
    hy.continuousOn (fun s _ => (hΦ.ode s y).hasDerivWithinAt)
    le_rfl t ⟨hat, le_rfl⟩

theorem suspension_flow_from_zero {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (fun y => SpatialExpression.suspensionField H y.2) Φ)
    (x y : Space) {t : ℝ} (ht : 0 ≤ t) :
    dist (Φ t x) (Φ t y) ≤ dist x y *
      Real.exp ((suspensionLipschitzBound H : ℝ) * t) := by
  simpa only [hΦ.initial, sub_zero] using suspension_flow_perturbation hH hT hΦ x y ht

end ForcedComputation

end

end OAI
