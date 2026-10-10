import OAI.Analysis.LienardCycles.HeightLimits

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ReferenceCharacteristic
open QuadraticCoordinates
lemma D_tendsto_zero (z k : ℝ) :
    Tendsto (fun r => D ((z,k),r)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have ht := (DN_analytic ((z,k),0)).continuousAt.tendsto.comp (model_tendsto z k)
  rw [DN_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (Hr_DN hr).symm
end QuinticLienard.ReferenceCharacteristic

end OAI
