import Mathlib
import OAI.Geometry.WeakMTW.Potentials.SmoothMetricLipschitz
import OAI.Geometry.WeakMTW.Potentials.IntermediateParameterFamily
import OAI.Geometry.WeakMTW.Potentials.UniformLocalLipschitz

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold NNReal
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem intermediate_uniform_pole_lipschitz (hMTW : HasWeakMTW (n := n) (M := M))
     {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
     ∃ C : ℝ≥0, ∀ d : IntermediateDatum M a b,
       LipschitzWith C (fun z => (datumInverse hMTW ha hb d z).1) := by
   have hloc (z : M) : ∃ r : ℝ, ∃ C : ℝ≥0, 0 < r ∧
       ∀ d : IntermediateDatum M a b,
         LipschitzOnWith C (fun y => (datumInverse hMTW ha hb d y).1) (Metric.ball z r ∩ univ) := by
     obtain ⟨K,hK,hKt,r,A,hr,hsrc,hparam⟩ := intermediate_parameter_family hMTW ha hab hb z
     have hsm (B : CovectorParameters n) (hB : B ∈ K) :
         ContMDiffAt 𝓘(ℝ,CovectorParameters n) (model n) 1 (fun B => (covectorFlow z B).1) B :=
       ((contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).contMDiffAt.comp B
         (covectorFlow_smooth z (hKt B hB))).of_le (by simp)
     obtain ⟨C,hC⟩ := ChartMetric.smooth_metric_compact_lipschitz hK hsm
     refine ⟨r,C*A,hr,?_⟩
     intro d
     apply LipschitzOnWith.of_dist_le_mul
     intro x hx y hy
     have hL := hC.comp (hparam d).2 (hparam d).1
     have hh := hL.dist_le_mul (x := x) hx.1 (y := y) hy.1
     simpa only [Function.comp_apply,datumParameter_flow hMTW ha hb z d (hsrc hx.1),
       datumParameter_flow hMTW ha hb z d (hsrc hy.1)] using hh
   obtain ⟨C,hC⟩ := UniformLocalLipschitz.globalize hloc (Metric.diam_nonneg (s := (univ : Set M)))
     (fun d x _ y _ => Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _))
   exact ⟨C,fun d => lipschitzOnWith_univ.mp (hC d)⟩
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
