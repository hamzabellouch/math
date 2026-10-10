import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.LocalMetricCharts
import OAI.Analysis.BiholderTransport.Geodesics.ChartLipschitz

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Metric Bundle
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section Charts
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_bilipschitz_chart (a : M) :
    ∃ C D : ℝ≥0, ∃ r>0, ball a r⊆(extChartAt 𝓘(ℝ,Model n) a).source ∧
      LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) a) (ball a r) ∧
      LipschitzOnWith D (extChartAt 𝓘(ℝ,Model n) a).symm
        (extChartAt 𝓘(ℝ,Model n) a '' ball a r) := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨C,r,hr,hs,hC⟩ := exists_lipschitzOn_chart (n := n) a
  obtain ⟨D,s,hspos,_,hD⟩ := exists_lipschitzOn_inverse_chart (E := Model n) a
  obtain ⟨t,ht,htsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (ball_mem_nhds a hr) ((continuousAt_extChartAt (I := 𝓘(ℝ,Model n)) a).preimage_mem_nhds
      (ball_mem_nhds _ hspos)))
  refine ⟨C,D,t,ht,fun x hx => hs (htsub hx).1,hC.mono (fun x hx => (htsub hx).1),?_⟩
  apply hD.mono
  rintro z ⟨x,hx,rfl⟩
  exact (htsub hx).2

variable [MeasurableSpace M] [BorelSpace M]
end Charts
end WeakMTWTransport

end

end

end

end OAI
