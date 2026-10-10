import OAI.Analysis.CircleDomains.Reflection.AnalyticStraighteningResidual
import OAI.Analysis.CircleDomains.Sobolev.RectangularL2

namespace OAI

/-! Holomorphicity of the actual finite straightening. The smooth
approximants have an L2-small antiholomorphic derivative on every closed
source rectangle; their locally uniform limit therefore satisfies Morera. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma straighteningApproximation_tendsto (D : AnalyticReflectionData C) :
    TendstoLocallyUniformly D.straighteningApproximation (D.principal ∘ D.comparison) atTop := by
  have h := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp D.limitData.forward
  exact h.comp D.comparison D.comparison.continuous

lemma straightening_holomorphic (D : AnalyticReflectionData C) :
    DifferentiableOn ℂ (D.principal ∘ D.comparison) ((↑) ⁻¹' C.region) := by
  obtain ⟨q,hq,he⟩ := D.exists_straightening_residual
  apply differentiableOn_of_vanishing_rectangle_errors
    (C.region_open.preimage OnePoint.continuous_coe)
    (fun n => ((D.approximation.smooth _).comp D.comparison_smooth).of_le (by simp))
    D.straighteningApproximation_tendsto
  intro z w hzw
  have hi := tendsto_doubleIntervalIntegral_L2 hq z.re w.re z.im w.im
  apply hi.congr'
  apply Eventually.of_forall
  intro n
  apply (doubleIntervalIntegral_congr_ae z w ?_).symm
  filter_upwards [he n] with p hp hpR
  exact hp (hzw hpR)

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
