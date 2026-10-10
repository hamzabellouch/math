import OAI.Analysis.CircleDomains.Topology.SphereChartInversePairs
import OAI.Analysis.CircleDomains.Uniformization.MobiusConformal

namespace OAI

/-! Every finite physical point has a chart neighborhood with a concrete
inverse Lipschitz bound. This is used only on compact coordinate slices. -/

open Set Function Filter Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem exists_sphereSliceChart (z : ℂ) :
    ∃ (B : ℝ≥0) (V : Set ℂ), IsOpen V ∧ z ∈ V ∧
      LipschitzOnWith B finiteCoord (((↑) : ℂ → Sphere) '' V) := by
  obtain ⟨B, W, hW, hB⟩ := finite_sphere_chart_inverse_pairs z
  have hc : Continuous (fun w : ℂ => (roundSphereEquiv (w : Sphere) : RoundAmbient)) :=
    continuous_subtype_val.comp (roundSphereEquiv.continuous.comp OnePoint.continuous_coe)
  obtain ⟨V, hVW, hV, hzV⟩ := _root_.mem_nhds_iff.mp (hc.continuousAt.preimage_mem_nhds hW)
  refine ⟨B, V, hV, hzV, LipschitzOnWith.of_dist_le_mul ?_⟩
  rintro _ ⟨w, hw, rfl⟩ _ ⟨u, hu, rfl⟩
  change dist w u ≤ (B : ℝ) *
    dist (roundSphereEquiv (w : Sphere) : RoundAmbient) (roundSphereEquiv (u : Sphere) : RoundAmbient)
  exact hB w u (hVW hw) (hVW hu)

 theorem finiteCoord_lipschitz_on_compact_chart {A : Set ℂ} (hA : IsCompact A) :
    ∃ B : ℝ≥0, LipschitzOnWith B finiteCoord (((↑) : ℂ → Sphere) '' A) := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hA.image OnePoint.continuous_coe)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨B, V, hV, hzV, hBV⟩ := exists_sphereSliceChart z
  refine ⟨B, ((↑) : ℂ → Sphere) '' V, mem_nhdsWithin_of_mem_nhds ?_, hBV⟩
  exact (OnePoint.isOpenEmbedding_coe.isOpenMap V hV).mem_nhds ⟨z, hzV, rfl⟩

end CircleDomainRigidity

end

end OAI
