import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalResolventWeak

namespace OAI

/-! Values of completed energy vectors, and consequently the constructed
Green operator, remain in the closure of genuine automorphic sections. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaGlobalInclusion_mem (u : cubicThetaGlobalEnergySpace) :
    cubicThetaGlobalInclusion u∈cubicThetaAutomorphicL2 := by
  let P := WithLp.fstL 2 ℂ CubicThetaGlobalL2 CubicThetaGradientL2
  have hr : cubicThetaGlobalEnergyGraph.range ≤ cubicThetaAutomorphicL2.comap P.toLinearMap := by
    rintro x ⟨F,rfl⟩
    change cubicThetaGlobalMass F∈cubicThetaAutomorphicL2
    exact Submodule.le_topologicalClosure _ ⟨F,rfl⟩
  have hc : IsClosed (cubicThetaAutomorphicL2.comap P.toLinearMap : Set CubicThetaGlobalEnergyAmbient) :=
    (Submodule.isClosed_topologicalClosure cubicThetaGlobalMass.range).preimage P.continuous
  exact cubicThetaGlobalEnergyGraph.range.topologicalClosure_minimal hr hc u.property

lemma cubicThetaGlobalGreen_mem (F : CubicThetaGlobalL2) :
    cubicThetaGlobalGreen F∈cubicThetaAutomorphicL2 := by
  rw [cubicThetaGlobalGreen_apply]
  exact cubicThetaGlobalInclusion_mem _

lemma cubicThetaGlobalResolvent_mem {z : ℂ} (hz : z.im≠0 ∨ z.re<1) (F : CubicThetaGlobalL2) :
    cubicThetaGlobalResolvent z F∈cubicThetaAutomorphicL2 := by
  rw [← cubicThetaGlobalResolventLift_value hz F]
  exact cubicThetaGlobalInclusion_mem _

end CubicFirstMoment

end

end OAI
