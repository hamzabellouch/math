import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarFlowSmooth
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.FlowVariational

namespace OAI

/-! Discharge of the smooth-dependence and variational-equation input for
the actual finite-expression planar transition. All analytic ingredients
are proved from the library implicit-function theorem and ODE uniqueness. -/

noncomputable section
namespace ForcedComputation
open ShearFlows
open scoped ContDiff

theorem variations_of_joint_smooth (V : ℝ → Plane → Plane)
    (Ω : ℝ → ℝ → Plane → Plane)
    (hVjoint : ContDiff ℝ ∞ (Function.uncurry V))
    (hs : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × Plane) => Ω p.1 p.2.1 p.2.2))
    (hΩ : IsPlanarTransition V Ω) : PlanarVariations V Ω := by
  have ha (a : ℝ) : ContDiff ℝ ∞ (Function.uncurry (Ω a)) :=
    hs.comp (contDiff_const.prodMk contDiff_id)
  have hV (a t : ℝ) : ContDiff ℝ ∞ (V (a + t)) :=
    hVjoint.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨fun a => funext (hΩ.initial a), ?_, ?_, ?_⟩
  · intro a t
    exact (ha a).comp (contDiff_const.prodMk contDiff_id)
  · intro a x v t
    exact Flow.first_variation (ha a) (hV a) (hΩ.ode a) t x v
  · intro a x v w t
    exact Flow.second_variation (ha a) (hV a) (hΩ.ode a) t x v w

theorem planarTransition_variations {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) {Ω : ℝ → ℝ → Plane → Plane}
    (hΩ : IsPlanarTransition (planarSlice H) Ω) :
    PlanarVariations (planarSlice H) Ω :=
  variations_of_joint_smooth (planarSlice H) Ω (planarSlice_joint_smooth hH)
    (planarTransition_joint_smooth hH hT hΩ) hΩ

theorem exists_planarTransition_with_variations {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) :
    ∃ Ω, IsPlanarTransition (planarSlice H) Ω ∧
      PlanarVariations (planarSlice H) Ω ∧
      ContDiff ℝ ∞ (fun p : ℝ × Plane => Ω p.1 (-p.1) p.2) := by
  obtain ⟨Ω, hΩ⟩ := exists_planarTransition hH hT
  exact ⟨Ω, hΩ, planarTransition_variations hH hT hΩ,
    planarTransition_backward_smooth hH hT hΩ⟩

end ForcedComputation

end

end OAI
