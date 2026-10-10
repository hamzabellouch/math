import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

/-! The real cluster values of a continuous path at a one-sided endpoint
contain every value between two of them. -/
noncomputable section
open Set Filter Metric
open scoped Topology

namespace SLEExactGauge

lemma endpoint_intermediate_level {f : ℝ → ℝ} {D a b c : ℝ}
    (hD : 0<D) (hC : ContinuousOn f (Ioo 0 D))
    (ha : MapClusterPt a (𝓝[>] (0:ℝ)) f) (hb : MapClusterPt b (𝓝[>] (0:ℝ)) f)
    (hac : a<c) (hcb : c<b) {δ : ℝ} (hδ : 0<δ) :
    ∃ t∈Ioo 0 δ, f t=c := by
  let ε := min δ D
  have hε : 0<ε := lt_min hδ hD
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), t∈Ioo 0 ε := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hε)] with t ht htε
    exact ⟨ht,htε⟩
  obtain ⟨u,hu,huε⟩ := ((ha.frequently (Iio_mem_nhds hac)).and_eventually hsmall).exists
  obtain ⟨v,hv,hvε⟩ := ((hb.frequently (Ioi_mem_nhds hcb)).and_eventually hsmall).exists
  have hcε : ContinuousOn f (Ioo 0 ε) := hC.mono (Ioo_subset_Ioo le_rfl (min_le_right δ D))
  obtain ⟨t,ht,he⟩ := isPreconnected_Ioo.intermediate_value huε hvε hcε ⟨hu.le,hv.le⟩
  exact ⟨t,⟨ht.1,ht.2.trans_le (min_le_left δ D)⟩,he⟩

theorem endpoint_cluster_interval {f : ℝ → ℝ} {D a b : ℝ}
    (hD : 0<D) (hC : ContinuousOn f (Ioo 0 D))
    (ha : MapClusterPt a (𝓝[>] (0:ℝ)) f) (hb : MapClusterPt b (𝓝[>] (0:ℝ)) f) :
    ∀ c∈Ioo a b, MapClusterPt c (𝓝[>] (0:ℝ)) f := by
  intro c hc
  apply clusterPt_iff_nonempty.mpr
  intro W hW V hV
  have hpre : f ⁻¹' V∈𝓝[>] (0:ℝ) := hV
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  obtain ⟨t,ht,he⟩ := endpoint_intermediate_level hD hC ha hb hc.1 hc.2 hδ
  have htB : t∈ball (0:ℝ) δ := by
    simpa only [mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht.1] using ht.2
  have hfV : f t∈V := hsub ⟨htB,ht.1⟩
  exact ⟨c,mem_of_mem_nhds hW,he ▸ hfV⟩

end SLEExactGauge

end

end OAI
