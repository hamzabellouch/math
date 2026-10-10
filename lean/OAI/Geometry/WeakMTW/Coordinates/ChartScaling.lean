import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.IntrinsicExp
import OAI.Geometry.WeakMTW.Coordinates.TangentCoordinates

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
open ChartMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

 theorem stateChart_mulState (x : M) (a : ℝ) (p : TangentBundle 𝓘(ℝ, E) M)
    (hp : p ∈ (stateChart x).source) :
    stateChart x (mulState a p) = ((stateChart x p).1,a • (stateChart x p).2) := by
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x
  have hb : p.1 ∈ e.baseSet := by
    simpa only [e,TangentBundle.trivializationAt_baseSet] using (stateChart_source x p).mp hp
  apply Prod.ext
  · rfl
  change (e ⟨p.1,a•p.2⟩).2 = a • (e p).2
  rw [← e.continuousLinearMapAt_apply_of_mem ℝ hb,
    ← e.continuousLinearMapAt_apply_of_mem ℝ hb,map_smul]

 theorem stateChart_symm_mul (x : M) (a : ℝ) {q : E × E}
    (hq : q ∈ (stateChart x).target) :
    (stateChart x).symm (q.1,a•q.2) = mulState a ((stateChart x).symm q) := by
  have hq' := (stateChart_target x q).mp hq
  rw [stateChart_symm x (q := (q.1,a•q.2)) hq',stateChart_symm x hq']
  change (⟨(chartAt E x).symm q.1,chartLift x q.1 (a•q.2)⟩ : TangentBundle 𝓘(ℝ, E) M) =
    ⟨(chartAt E x).symm q.1,a•chartLift x q.1 q.2⟩
  rw [map_smul]

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
