import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.BilinearMetricSpeedSquare
import OAI.Analysis.BiholderTransport.LocalFlow.NormalFlow

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma metric_curve_speed_square {γ : ℝ → M} {t k : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ γ t)
    (hd : ∀ᶠ s in 𝓝 t, dist (γ t) (γ s) = |s-t| * k) :
    ‖mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t (1:ℝ)‖^2 = k^2 := by
  let a := γ t
  let c := extChartAt 𝓘(ℝ,E) a
  let q : ℝ → E := c ∘ γ
  let g := riemannianCoordinateMetric (E := E) a (c a)
  obtain ⟨δ,_,τ,hδ,_,hτ,_,_,_,e,_,_,_,_,_,hes,he0,_,hed,hei,_,hdist,hD⟩ :=
    exists_metric_normal_flow (E := E) a
  have hqat : q t ∈ e.target := by change c a ∈ e.target; rw [←he0]; exact e.map_source hes
  have hq : ContDiffAt ℝ ∞ q t :=
    ((contMDiffAt_extChartAt (I := 𝓘(ℝ,E)) (x := a)).comp t hγ).contDiffAt
  let f : ℝ → E := e.symm ∘ q
  have hf : ContDiffAt ℝ ∞ f t :=
    (hei.contDiffAt (e.open_target.mem_nhds hqat)).comp t hq
  have hf0 : f t = 0 := by
    change e.symm (c a) = 0
    rw [←he0]; exact e.left_inv hes
  have hn : ∀ᶠ s in 𝓝 t, γ s ∈ Metric.ball a δ :=
    hγ.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds a hδ)
  have hgs : ∀ᶠ s in 𝓝 t, g (f s) (f s) = (k^2/τ^2)*(s-t)^2 := by
    filter_upwards [hn,hd] with s hs hds
    have H : τ^2 * g (f s) (f s) = (s-t)^2*k^2 := by
      calc
        _ = (τ * Real.sqrt (g (f s) (f s)))^2 := by
          rw [mul_pow,Real.sq_sqrt (positive_bilinear_nonneg g
            (fun v hv => riemannianCoordinateMetric_positive (mem_extChartAt_target a) hv) _)]
        _ = dist (γ t) (γ s)^2 := by rw [hdist (γ s) hs]; rfl
        _ = _ := by rw [hds,mul_pow,sq_abs]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (pow_ne_zero 2 hτ.ne')).mpr
    nlinarith [H]
  have hjet := bilinear_metric_speed_of_square hf hf0 hgs
  have hedf : HasDerivAt (fun s => e (f s)) (τ • deriv f t) t := by
    have H := (hed.contDiffAt (e.open_source.mem_nhds hes)).differentiableAt (by simp)
    have H' : HasFDerivAt e (τ • ContinuousLinearMap.id ℝ E) (f t) := by
      rw [hf0]; rw [←hD]; exact H.hasFDerivAt
    simpa only [Function.comp_def,smul_apply,ContinuousLinearMap.id_apply] using
      H'.comp_hasDerivAt t (hf.differentiableAt (by simp)).hasDerivAt
  have heq : (fun s => e (f s)) =ᶠ[𝓝 t] q := by
    filter_upwards [hq.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds hqat)] with s hs
    exact e.right_inv hs
  have hqder : deriv q t = τ • deriv f t :=
    (hedf.congr_of_eventuallyEq heq.symm).deriv
  have hspeed : g (deriv q t) (deriv q t) = k^2 := by
    simp only [hqder,map_smul,smul_apply,smul_eq_mul,hjet]
    field_simp [hτ.ne']
  have hm := mfderiv_comp t (mdifferentiableAt_extChartAt
    (I := 𝓘(ℝ,E)) (mem_chart_source E a)) (hγ.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hm
  have hval : deriv q t = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c a
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1) :=
    congrArg (fun L : ℝ →L[ℝ] E => L 1) hm
  have hnorm := coordinate_metric_chart_derivative_norm (mem_extChartAt_source (I := 𝓘(ℝ,E)) a)
    (g := g) (by
      intro u v
      change riemannianCoordinateMetric a (c a) u v = _
      rw [riemannianCoordinateMetric_apply,c.left_inv (mem_extChartAt_source (I := 𝓘(ℝ,E)) a)])
    (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1)
  rw [←hval] at hnorm
  calc
    _ = (Real.sqrt (g (deriv q t) (deriv q t)))^2 :=
      congrArg (fun x : ℝ => x^2) hnorm.symm
    _ = g (deriv q t) (deriv q t) := Real.sq_sqrt (positive_bilinear_nonneg g
      (fun v hv => riemannianCoordinateMetric_positive (mem_extChartAt_target a) hv) _)
    _ = k^2 := hspeed

end WeakMTWTransport

end

end OAI
