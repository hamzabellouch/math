import OAI.NumberTheory.CubicMoment.Theta.CubicThetaChartTransition
import Mathlib.Geometry.Manifold.IsManifold.Basic

namespace OAI

/-! The actual principal quotient is a smooth real three-dimensional
manifold. Chart changes are the already proved smooth arithmetic actions. -/
noncomputable section
open scoped ContDiff Manifold
namespace CubicFirstMoment

lemma cubicThetaQuotientChart_transition_contDiff (p q : CubicThetaQuotient) :
    ContDiffOn ℝ ∞ ((cubicThetaQuotientChart p).symm.trans (cubicThetaQuotientChart q))
      ((cubicThetaQuotientChart p).symm.trans (cubicThetaQuotientChart q)).source := by
  intro x hx
  let e := cubicThetaCoveringChart (cubicThetaQuotientLift p)
  let f := cubicThetaCoveringChart (cubicThetaQuotientLift q)
  have hsource : x∈cubicThetaChartTransitionSource e f := by
    change (x∈cubicThetaPointInclusion.target ∧ cubicThetaPointInclusion.symm x∈e.source) ∧
      (e (cubicThetaPointInclusion.symm x)∈f.target ∧
      f.symm (e (cubicThetaPointInclusion.symm x))∈cubicThetaPointInclusion.source) at hx
    exact ⟨hx.1.1,hx.1.2,hx.2.1⟩
  have h := cubicThetaChartTransition_contDiffAt e f
    (cubicThetaCoveringChart_coe _) (cubicThetaCoveringChart_coe _) hsource
  exact h.contDiffWithinAt

instance cubicThetaQuotient_isManifold :
    IsManifold (𝓘(ℝ,ℂ × ℝ)) ∞ CubicThetaQuotient := by
  apply isManifold_of_contDiffOn
  rintro e f ⟨p,rfl⟩ ⟨q,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.comp_id,
    Function.id_comp,Set.preimage_id_eq,Set.range_id,Set.inter_univ,id_eq] using
    cubicThetaQuotientChart_transition_contDiff p q

end CubicFirstMoment

end

end OAI
