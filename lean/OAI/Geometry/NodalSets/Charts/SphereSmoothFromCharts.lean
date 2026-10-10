import OAI.Geometry.NodalSets.Charts.SphereChartOpenMap
import OAI.Geometry.NodalSets.Charts.SphereDifferentialCoordinates

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff Topology
noncomputable section

lemma sphere_smooth_of_chart_pullbacks (f : Base → ℝ)
    (hf : ∀ p, ContDiff ℝ ∞ (f ∘ sphereChartCoordMap p)) :
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f := by
  intro x
  have hc := contMDiffAt_extChartAt' (I := 𝓡 4) (n := ∞) (x := x) (x' := x)
    (mem_chart_source BaseModel x)
  have hh := (((hf x).comp seedCoordEquiv.symm.contDiff).contMDiff.contMDiffAt).comp x hc
  apply hh.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := 𝓡 4) x).mem_nhds (mem_extChartAt_source (I := 𝓡 4) x)] with y hy
  simp only [Function.comp_apply,sphereChartCoordMap,seedCoordEquiv.apply_symm_apply,
    (extChartAt (𝓡 4) x).left_inv hy]

end
end Yau.Target

end OAI
