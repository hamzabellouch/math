import OAI.Geometry.NodalSets.Charts.ChartedEnvelope
import OAI.Geometry.NodalSets.Elliptic.LocalDirection

namespace OAI

namespace Yau.Geometry
open Filter
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma sourceHessian_continuous (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ y v, v ≠ 0 → 0 < g y v v)
    (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S) : Continuous (sourceHessian g S) := by
  have hD := hS.continuous_fderiv (by simp)
  exact ((hS.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)).sub
    (((ContinuousLinearMap.compL ℝ Coord Coord ℝ).continuous.comp hD).clm_comp
      (smooth_metric_connection_continuous g hg hp))

variable {T : Type*} [TopologicalSpace T]

theorem exists_admissible_chart_patch
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (y : T → Coord) (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0)
    (t0 : T) (q0 : Coord) (hperp : g (y t0) (metricGradient g S (y t0)) q0 = 0)
    (hlen : g (y t0) q0 q0 = g (y t0) (metricGradient g S (y t0)) (metricGradient g S (y t0))+4)
    (hstrict : 0 < sourceHessian g S (y t0) (metricGradient g S (y t0)) (metricGradient g S (y t0))+
      sourceHessian g S (y t0) q0 q0) :
    ∃ (U : Set T) (ht0 : t0 ∈ U), U ∈ 𝓝 t0 ∧ ∃ q : U → Coord,
      Continuous q ∧ q ⟨t0,ht0⟩ = q0 ∧
      (∀ t : U, g (y t) (metricGradient g S (y t)) (q t) = 0 ∧
        g (y t) (q t) (q t) = g (y t) (metricGradient g S (y t)) (metricGradient g S (y t))+4 ∧
        0 < sourceHessian g S (y t) (metricGradient g S (y t)) (metricGradient g S (y t))+
          sourceHessian g S (y t) (q t) (q t)) ∧
      ∃ V : Set U, V ∈ 𝓝 (⟨t0,ht0⟩ : U) ∧ ∃ e : V → Coord ≃L[ℝ] Coord,
        Continuous (fun t ↦ (e t).toContinuousLinearMap) ∧
        (∀ t : V, e t (Pi.single 0 1) = metricNormalize (g (y t.val.val)) (metricGradient g S (y t.val.val)) ∧
          e t (Pi.single 1 1) = metricNormalize (g (y t.val.val)) (q t.val)) ∧
        (∀ (t : V) i j, pullbackMetric g (actualMetricChart g (y t.val.val) (e t)) 0
          (Pi.single i 1) (Pi.single j 1) = if i=j then 1 else 0) ∧
        (∀ (t : V) u v, fderiv ℝ (fun x ↦ pullbackMetric g (actualMetricChart g (y t.val.val) (e t)) x u v) 0 = 0) ∧
        ∀ k, Continuous (fun z : V × Coord ↦ iteratedFDeriv ℝ k
          (actualMetricChart g (y z.1.val.val) (e z.1) : Coord → Coord) z.2) := by
  have hpc := (metricGradient_continuous g hg hp S hS).comp hy
  obtain ⟨U,q,hU,hq,hq0,hqprop⟩ := continue_admissible_direction
    (fun t ↦ g (y t)) (fun t ↦ sourceHessian g S (y t)) (hg.continuous.comp hy)
    ((sourceHessian_continuous g hg hp S hS).comp hy) (fun t ↦ hp (y t))
    (fun t ↦ metricGradient g S (y t)) hpc hp0 t0 q0 hperp hlen hstrict
  have ht0 : t0 ∈ U := mem_of_mem_nhds hU
  have hqc : Continuous (fun t : U ↦ q t) := continuousOn_iff_continuous_domRestrict.mp hq
  have hqn : ∀ t : U, q t ≠ 0 := by
    intro t hzero
    have hh := (hqprop t t.property).2.1
    simp only [hzero, map_zero] at hh
    have hp' := hp (y t) (metricGradient g S (y t)) (hp0 t)
    linarith
  obtain ⟨V,hV,e,he,haxes,_,hM0,hM1,hjets,_⟩ := exists_actual_adapted_chart_family g hg hs hp
    (fun t : U ↦ y t) (fun t : U ↦ metricGradient g S (y t)) (fun t : U ↦ q t)
    (hy.comp continuous_subtype_val) (hpc.comp continuous_subtype_val) hqc (fun t ↦ hp0 t) hqn
    (fun t ↦ (hqprop t t.property).1) ⟨t0,ht0⟩
  exact ⟨U,ht0,hU,(fun t : U ↦ q t),hqc,hq0,(fun t ↦ hqprop t t.property),
    V,hV,e,he,haxes,hM0,hM1,hjets⟩

end
end Yau.Geometry

end OAI
