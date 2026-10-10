import Mathlib
import OAI.Analysis.BiholderTransport.Volume.RadialCalibration
import OAI.Analysis.BiholderTransport.Coordinates.CoordinateMetricNorm
import OAI.Analysis.BiholderTransport.Coordinates.TangentLift
import OAI.Analysis.BiholderTransport.CostGeometry.LinearRadialDerivative
import OAI.Analysis.BiholderTransport.CostGeometry.RadialVelocityMetricEqualities

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

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma normal_chart_radial_rigidity
    (e : OpenPartialHomeomorph E E)
    (hed : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (g₀ : E →L[ℝ] E →L[ℝ] ℝ) (hs₀ : ∀ u v, g₀ u v = g₀ v u)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (V : E → E) (τ k : ℝ)
    (hp : ∀ v ∈ e.source, ∀ w : E, w ≠ 0 → 0 < g (e v) w w)
    (hs : ∀ v ∈ e.source, ∀ u w, g (e v) u w = g (e v) w u)
    (henergy : ∀ v ∈ e.source, g (e v) (V v) (V v) = g₀ v v)
    (hgauss : ∀ v ∈ e.source, ∀ w,
      g (e v) (V v) (fderiv ℝ e v w) = τ*g₀ v w)
    (hradial : ∀ v ∈ e.source, fderiv ℝ e v v = τ • V v)
    {f : ℝ → E} {l r a : ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo l r))
    (ha : a ∈ Ioo l r) (himg : MapsTo f (Ioo l r) e.source)
    (hspeed : ∀ s ∈ Ioo l r,
      g (e (f s)) (deriv (e ∘ f) s) (deriv (e ∘ f) s) = k^2)
    (hdist : ∀ s ∈ Ioo l r, τ^2*g₀ (f s) (f s) = (s-a)^2*k^2) :
    ∀ s ∈ Ioo l r, f s = (s-a) • deriv f a := by
  apply linear_of_radial_derivative hf ha
  intro s hs'
  have hfs := himg hs'
  have hfD := (hf.contDiffAt (isOpen_Ioo.mem_nhds hs')).differentiableAt (by simp)
  have heD := (hed.contDiffAt (e.open_source.mem_nhds hfs)).differentiableAt (by simp)
  have hiD := (hei.contDiffAt (e.open_target.mem_nhds (e.map_source hfs))).differentiableAt (by simp)
  have hqder : deriv (e ∘ f) s = fderiv ℝ e (f s) (deriv f s) :=
    (heD.hasFDerivAt.comp_hasDerivAt s hfD.hasDerivAt).deriv
  have heq : (fun t => τ^2*g₀ (f t) (f t)) =ᶠ[𝓝 s] (fun t => (t-a)^2*k^2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs'] with t ht
    exact hdist t ht
  have hpair := bilinear_metric_radial_derivative hs₀ hfD heq
  have hvelocity : (s-a) • deriv (e ∘ f) s = τ • V (f s) := by
    apply radial_velocity_of_metric_equalities (hp _ hfs) (hs _ hfs) (hspeed s hs')
    · rw [henergy _ hfs]; exact hdist s hs'
    · rw [hqder,hgauss _ hfs]
      nlinarith [hpair]
  have hL : (fderiv ℝ e.symm (e (f s))).comp (fderiv ℝ e (f s)) =
      ContinuousLinearMap.id ℝ E := by
    have H := fderiv_partial_homeomorph_right_inverse e.symm hfs
      (by simpa only [OpenPartialHomeomorph.symm_symm] using hiD) heD
    simpa only [OpenPartialHomeomorph.symm_symm,e.left_inv hfs] using H
  have hinj : Function.Injective (fderiv ℝ e (f s)) := by
    intro u v huv
    have H := congrArg (fderiv ℝ e.symm (e (f s))) huv
    simpa only [←ContinuousLinearMap.comp_apply,hL,ContinuousLinearMap.id_apply] using H
  apply hinj
  rw [map_smul,←hqder,hradial _ hfs]
  exact hvelocity
end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

omit [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma coordinate_curve_speed_square {γ : ℝ → M} {t : ℝ} {a : M}
    (hγ : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t)
    (ha : γ t ∈ (extChartAt 𝓘(ℝ,E) a).source) :
    riemannianCoordinateMetric a (extChartAt 𝓘(ℝ,E) a (γ t))
      (deriv (extChartAt 𝓘(ℝ,E) a ∘ γ) t) (deriv (extChartAt 𝓘(ℝ,E) a ∘ γ) t) =
      ‖mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t (1:ℝ)‖^2 := by
  let c := extChartAt 𝓘(ℝ,E) a
  let g := riemannianCoordinateMetric a (c (γ t))
  have hm := mfderiv_comp t (mdifferentiableAt_extChartAt
    (I := 𝓘(ℝ,E)) (x := a) (by simpa only [extChartAt_source] using ha)) hγ
  rw [mfderiv_eq_fderiv] at hm
  have hval : deriv (c ∘ γ) t = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c (γ t)
      (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1) :=
    congrArg (fun L : ℝ →L[ℝ] E => L 1) hm
  have hnorm := coordinate_metric_chart_derivative_norm ha
    (g := g) (by
      intro u v
      change riemannianCoordinateMetric a (c (γ t)) u v = _
      rw [riemannianCoordinateMetric_apply,c.left_inv ha])
    (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t 1)
  rw [←hval] at hnorm
  calc
    _ = (Real.sqrt (g (deriv (c ∘ γ) t) (deriv (c ∘ γ) t)))^2 :=
      (Real.sq_sqrt (positive_bilinear_nonneg g
        (fun v hv => riemannianCoordinateMetric_positive (c.map_source ha) hv) _)).symm
    _ = _ := congrArg (fun x : ℝ => x^2) hnorm

omit [FiniteDimensional ℝ E] [IsRiemannianManifold 𝓘(ℝ,E) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma coordinate_curve_derivative_at_center {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t) :
    deriv (extChartAt 𝓘(ℝ,E) (γ t) ∘ γ) t =
      mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t (1:ℝ) := by
  have H := mfderiv_comp t (mdifferentiableAt_extChartAt
    (I := 𝓘(ℝ,E)) (mem_chart_source E (γ t))) hγ
  rw [mfderiv_eq_fderiv,mfderiv_extChartAt_self] at H
  exact congrArg (fun L : ℝ →L[ℝ] E => L 1) H

end WeakMTWTransport

end

end OAI
