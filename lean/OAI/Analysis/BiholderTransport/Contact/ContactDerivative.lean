import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.PoleCoordinates

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff

namespace WeakMTWTransport
section ContactDerivative
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def coordinateContact (a b : M) (q : Model n × (Model n →L[ℝ] ℝ)) : Model n :=
  extChartAt 𝓘(ℝ,Model n) b (coordinateBackward a (-1,q.1,q.2))

omit [Nonempty M] in
lemma coordinateContact_contDiffAt {a b : M} {q : Model n × (Model n →L[ℝ] ℝ)}
    (hq : q.1∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hb : coordinateBackward a (-1,q.1,q.2)∈(extChartAt 𝓘(ℝ,Model n) b).source) :
    ContDiffAt ℝ ∞ (coordinateContact (n := n) a b) q := by
  have hi : ContDiffAt ℝ ∞ (fun z : Model n × (Model n →L[ℝ] ℝ) => ((-1:ℝ),z)) q :=
    contDiffAt_const.prodMk contDiffAt_id
  have hq' := (coordinateBackward_contMDiffAt (q := (-1,q.1,q.2)) hq).comp q
    hi.contMDiffAt
  have hb' : coordinateBackward a (-1,q.1,q.2)∈(chartAt (Model n) b).source := by
    simpa only [extChartAt_source] using hb
  exact ((contMDiffAt_extChartAt' hb').comp q hq').contDiffAt
end ContactDerivative
end WeakMTWTransport

end

end

end

end OAI
