import Mathlib
import OAI.Geometry.WeakMTW.Potentials.ChartLocalLipschitz

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold NNReal
namespace ChartMetric
noncomputable section
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

 theorem smooth_metric_local_lipschitz {f : V → M} {a : V}
     (hf : ContMDiffAt 𝓘(ℝ,V) 𝓘(ℝ,E) 1 f a) :
     ∃ C : ℝ≥0, ∃ U ∈ 𝓝 a, LipschitzOnWith C f U := by
   let c := chartAt E (f a)
   have ha : f a ∈ c.source := mem_chart_source E (f a)
   obtain ⟨r,B,hr,_hB,_hT,hL⟩ := chart_inverse_local_lipschitz (E := E) (f a)
   have hcoord : ContDiffAt ℝ 1 (c ∘ f) a := contMDiffAt_iff_contDiffAt.mp
     (((contMDiffOn_chart (n := 1)).contMDiffAt (c.open_source.mem_nhds ha)).comp a hf)
   obtain ⟨C,U,hU,hUL⟩ := hcoord.exists_lipschitzOnWith
   have hnb : c.source ∩ c ⁻¹' Metric.ball (c (f a)) r ∈ 𝓝 (f a) :=
     inter_mem (c.open_source.mem_nhds ha)
       ((c.continuousAt ha).preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
   let W := U ∩ f ⁻¹' (c.source ∩ c ⁻¹' Metric.ball (c (f a)) r)
   refine ⟨B*C,W,inter_mem hU (hf.continuousAt.preimage_mem_nhds hnb),?_⟩
   apply LipschitzOnWith.of_dist_le_mul
   intro x hx y hy
   have hd := hL.dist_le_mul (x := c (f x)) hx.2.2 (y := c (f y)) hy.2.2
   rw [c.left_inv hx.2.1,c.left_inv hy.2.1] at hd
   exact hd.trans (by
     rw [NNReal.coe_mul,mul_assoc]
     exact mul_le_mul_of_nonneg_left (hUL.dist_le_mul (x := x) hx.1 (y := y) hy.1) B.coe_nonneg)

 theorem smooth_metric_compact_lipschitz {f : V → M} {K : Set V} (hK : IsCompact K)
     (hf : ∀ a ∈ K, ContMDiffAt 𝓘(ℝ,V) 𝓘(ℝ,E) 1 f a) :
     ∃ C : ℝ≥0, LipschitzOnWith C f K := by
   apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
   intro a ha
   obtain ⟨C,U,hU,hL⟩ := smooth_metric_local_lipschitz (hf a ha)
   exact ⟨C,U,mem_nhdsWithin_of_mem_nhds hU,hL⟩
end
end ChartMetric
end

end WeakMTWGlobalSupport

end OAI
