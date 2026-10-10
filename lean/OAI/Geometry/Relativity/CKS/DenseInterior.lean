import OAI.Geometry.Relativity.CKS.LocalConstraints

namespace OAI

noncomputable section
open Manifold Set Filter
open scoped ContDiff Topology
namespace CKSIntrinsicTopology
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
lemma dense_interior : Dense (I.interior M) := by
  intro x
  let u := extChartAt I x x
  have hu : u ∈ (extChartAt I x).target := mem_extChartAt_target x
  have hcl : u ∈ closure (interior (range I)) :=
    I.range_subset_closure_interior (extChartAt_target_subset_range x hu)
  let : NeBot (𝓝[interior (range I)] u) := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hcont : ContinuousWithinAt (extChartAt I x).symm (range I) u :=
    (mdifferentiableWithinAt_extChartAt_symm hu).continuousWithinAt
  have ht : Tendsto (extChartAt I x).symm (𝓝[interior (range I)] u) (𝓝 x) := by
    simpa only [ContinuousWithinAt,u,extChartAt_to_inv] using hcont.mono interior_subset
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,
    (nhdsWithin_mono u interior_subset) (extChartAt_target_mem_nhdsWithin x)] with y hy hty
  have hiny : y ∈ interior (extChartAt I x).target := by
    apply mem_interior_iff_mem_nhds.mpr
    have hn := extChartAt_target_mem_nhdsWithin_of_mem hty
    rwa [nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hy)] at hn
  apply (I.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
    (chart_mem_atlas H x) (by simpa only [extChartAt_source] using (extChartAt I x).map_target hty)).mpr
  change extChartAt I x ((extChartAt I x).symm y) ∈ interior (extChartAt I x).target
  rwa [(extChartAt I x).right_inv hty]
end CKSIntrinsicTopology

end

end OAI
