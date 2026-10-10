import OAI.Geometry.Relativity.CKS.FoliationFrameRegularity
import OAI.Geometry.Relativity.CKS.PhysicalMomentumCoordinate

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter CKSFrame
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

theorem physical_foliation_constraints {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point}
    {K : PhysicalPoint → AmbientMat} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef)
    (hk : DifferentiableAt ℝ K x) (hks : ∀ᶠ y in 𝓝 x, (K y).IsHermitian) :
    let G := fun y => foliationMetric (U y) (γ y) (s y)
    let E := fun i y => adaptedFrame (U y) (γ y) (s y) i
    let c := frameConnectionField G E x
    let dc := fun a => connectionFieldDerivative (frameConnectionField G E) (E a x) x
    let t := frameTensorData K E x
    let dt := frameTensorDerivativeData K E x
    (actualFrameScalar G E x+((G x)⁻¹*K x).trace^2-
        ((G x)⁻¹*K x*(G x)⁻¹*K x).trace)/2 =
      leafScalar c dc/2-normalMean dc+accelDiv c dc-accelNormSq c-
        3/4*(mean c)^2-shearNormSq c/2+t.L*t.p+t.p^2/4-tauNormSq t/2-etaNormSq t ∧
    coordinateMomentum G K x (E 0 x) =
      mean c*(t.L-t.p/2)-shearTau c t-(dt 0).p+etaDiv c t dt-2*etaAcceleration c t ∧
    ∀ a, coordinateMomentum G K x (E a.succ x) =
      normalLieEta c t dt a+mean c*t.eta a+tauDiv c t dt a-
        ((dt a.succ).L+(dt a.succ).p/2)+accelTensor c t a := by
  dsimp only
  have h := foliation_actualAdaptedAt hU hγ hs h0.ne' hp
  constructor
  · rw [← actualFrameEnergy_coordinate h.self_of_nhds hks.self_of_nhds,
      actualFrame_energy_representation h hks.self_of_nhds]
    exact energy_decomposition _ _ _
  constructor
  · rw [← actualFrameMomentum_coordinate h.self_of_nhds hk,
      actualFrame_momentum_representation h.self_of_nhds hks]
    exact normal_momentum_decomposition _ _ _
  · intro a
    rw [← actualFrameMomentum_coordinate h.self_of_nhds hk,
      actualFrame_momentum_representation h.self_of_nhds hks]
    exact tangential_momentum_decomposition _ _ _ a

end
end CKSAngularGeometry

end

end OAI
