import OAI.MathematicalPhysics.RapidForcing.CurlDerivatives
import OAI.MathematicalPhysics.RapidForcing.JointSmoothness

namespace OAI

open scoped BigOperators ENNReal Topology
open Set MeasureTheory
namespace RapidForcing

lemma classical_of_joint_smooth {u : Field Space} {p : Field ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry u))
    (hp : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry p)) : Classical u p := by
  refine ⟨?_, ?_, ?_⟩
  · intro t _
    constructor
    · exact (hu.comp (contDiff_const.prodMk contDiff_id)).of_le
        (WithTop.coe_le_coe.mpr le_top)
    · exact (hp.comp (contDiff_const.prodMk contDiff_id)).of_le
        (WithTop.coe_le_coe.mpr le_top)
  · intro x
    exact (hu.comp (contDiff_id.prodMk contDiff_const)).differentiable
      (by simp) |>.differentiableOn
  · intro T _
    refine ⟨hu.continuous.continuousOn, ?_, ?_, ?_, hp.continuous.continuousOn, ?_⟩
    · apply (ordinaryTimeD_joint_smooth hu).continuous.continuousOn.congr
      intro z hz
      exact timeD_eq_ordinary hu hz.1.1 z.2
    · intro i
      exact (spatialD_joint_smooth hu i).continuous.continuousOn
    · intro i j
      exact (spatialD_joint_smooth (spatialD_joint_smooth hu j) i).continuous.continuousOn
    · intro i
      exact (spatialD_joint_smooth hp i).continuous.continuousOn

theorem addressed_classical_solution (ν : ℝ) (M : Machine) (w : M.Input) :
    let u := addressedVelocity M w
    let f := addressedForce ν M w
    Smooth f ∧ Supported f ∧ Smooth u ∧ Supported u ∧
      Classical u (fun _ _ => 0) ∧ NavierStokes ν f u (fun _ _ => 0) := by
  exact ⟨(addressed_fields_smooth ν M w).2, addressedForce_supported ν M w,
    (addressed_fields_smooth ν M w).1, addressedVelocity_supported M w,
    classical_of_joint_smooth (addressedVelocity_joint_smooth M w) contDiff_const,
    addressed_pointwise_equations ν M w⟩

end RapidForcing

end OAI
