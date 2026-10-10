import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.SprayProjection
import OAI.Analysis.BiholderTransport.Coordinates.JointNormalChart
import OAI.Analysis.BiholderTransport.Coordinates.NormalGradient

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

lemma exists_local_metric_gradient (a : M) :
    ∃ δ τ : ℝ, 0 < δ ∧ 0 < τ ∧
      Metric.ball a δ ⊆ (extChartAt 𝓘(ℝ,E) a).source ∧
      ∀ b ∈ Metric.ball a δ, ∀ y ∈ Metric.ball a δ,
      ∃ z : TangentBundle 𝓘(ℝ,E) M,
        z.1 = b ∧ (sprayFlow τ z).1 = y ∧ dist b y = τ * ‖z.2‖ ∧
        HasFDerivAt (fun w : E => dist b ((extChartAt 𝓘(ℝ,E) a).symm w)^2 / 2)
          (τ • riemannianCoordinateMetric a (extChartAt 𝓘(ℝ,E) a y)
            ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E))
              (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) (sprayFlow τ z)).2))
          (extChartAt 𝓘(ℝ,E) a y) := by
  obtain ⟨δ,r,τ,hδ,hr,hτ,hτr,Φ,e,hΦ,hΦ0,hode,he,hesub,hed,hei,hsrc,hdiag,htarget,hdist⟩ :=
    exists_uniform_metric_normal_coordinates (E := E) a
  refine ⟨δ,τ,hδ,hτ,hsrc,?_⟩
  intro b hb y hy
  let c := extChartAt 𝓘(ℝ,E) a
  let A : TangentBundle 𝓘(ℝ,E) M := ⟨a,0⟩
  let χ := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) A
  let g := riemannianCoordinateMetric (E := E) a
  have hp : ∀ z : E × E, (e z).1 = z.1 := by intro z; rw [he]
  let f := fiberwiseHomeomorph e hp (c b)
  let v := f.symm (c y)
  have hyt : c y ∈ f.target := htarget b hb y hy
  have hvs : v ∈ f.source := f.map_target hyt
  have hcb : dist (c b) (c a) < r :=
    (max_lt_iff.mp (show max (dist (c b) (c a)) (dist (0:E) 0) < r from hesub (hdiag b hb))).1
  have hball : ∀ w ∈ Metric.ball (0:E) r, (c b,w) ∈ Metric.ball (c a,0) r := by
    intro w hw
    exact max_lt hcb hw
  have hv : v ∈ Metric.ball (0:E) r :=
    (max_lt_iff.mp (show max (dist (c b) (c a)) (dist v 0) < r from hesub hvs)).2
  let Ψ : ℝ × E → E := fun z => (Φ (z.1,(c b,z.2))).1
  let W : ℝ × E → E := fun z => (Φ (z.1,(c b,z.2))).2
  have hΦc := hΦ.comp (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd))
    (show MapsTo (fun z : ℝ × E => (z.1,(c b,z.2)))
      (Ioo (-r) r ×ˢ Metric.ball 0 r) (Ioo (-r) r ×ˢ Metric.ball (c a,0) r) from
      fun z hz => ⟨hz.1,hball z.2 hz.2⟩)
  have hf : (f : E → E) = fun w => Ψ (τ,w) := by
    funext w
    change (e (c b,w)).2 = _
    rw [he]
  have ht : τ ∈ Ioo (-r) r := ⟨by linarith,hτr⟩
  have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨by linarith,hr⟩
  have hΨv : Ψ (τ,v) = c y := (congrFun hf v).symm.trans (f.right_inv hyt)
  have hG : ∀ w : E, g (c y) (W (τ,v)) (fderiv ℝ f v w) = τ*g (c b) v w := by
    intro w
    rw [hf,←hΨv]
    exact coordinate_endpoint_gauss (Ψ := Ψ) (W := W) (x := c b) (g := g)
      (isOpen_extChartAt_target a)
      (contDiffOn_riemannianCoordinateMetric a)
      (fun _ hx => riemannianCoordinateMetric_isInvertible hx)
      (fun x _ u v => riemannianCoordinateMetric_symm a x u v)
      (show ContDiffOn ℝ ∞ Ψ (Ioo (-r) r ×ˢ Metric.ball 0 r) from hΦc.fst)
      (show ContDiffOn ℝ ∞ W (Ioo (-r) r ×ˢ Metric.ball 0 r) from hΦc.snd)
      (fun t ht w hw => (hode t ht (c b,w) (hball w hw)).1)
      (fun t ht w hw => ⟨((hode t ht (c b,w) (hball w hw)).2).fst,
        ((hode t ht (c b,w) (hball w hw)).2).snd⟩) h0
      (fun w hw => congrArg Prod.fst (hΦ0 (c b,w) (hball w hw)))
      (fun w hw => congrArg Prod.snd (hΦ0 (c b,w) (hball w hw))) ht hv w
  have hfd := ((fiberwiseHomeomorph_contDiffOn hp (c b) hed).contDiffAt
    (f.open_source.mem_nhds hvs)).differentiableAt (by simp)
  have hfi := ((fiberwiseHomeomorph_symm_contDiffOn hp (c b) hei).contDiffAt
    (f.open_target.mem_nhds hyt)).differentiableAt (by simp)
  have hD := normal_action_hasFDerivAt f hyt hfd hfi (g (c b)) (g (c y))
    (riemannianCoordinateMetric_symm a (c b)) (W (τ,v)) τ hG
  have hnear : ∀ᶠ w : E in 𝓝 (c y), w ∈ c.target ∧ c.symm w ∈ Metric.ball a δ := by
    have hcy : c y ∈ c.target := c.map_source (hsrc hy)
    have hynear := ((continuousOn_extChartAt_symm a).continuousAt ((isOpen_extChartAt_target a).mem_nhds hcy)).preimage_mem_nhds
      (by rw [c.left_inv (hsrc hy)]; exact Metric.isOpen_ball.mem_nhds hy)
    filter_upwards [(isOpen_extChartAt_target a).mem_nhds hcy, hynear] with w hw hwy
    exact ⟨hw,hwy⟩
  have hdistEq : (fun w : E => dist b (c.symm w)^2/2) =ᶠ[𝓝 (c y)]
      (fun w => (τ^2/2)*g (c b) (f.symm w) (f.symm w)) := by
    filter_upwards [hnear] with w hw
    have hwt : w ∈ f.target := by
      change (c b,w) ∈ e.target
      have hh : (c b,c (c.symm w)) ∈ e.target := htarget b hb (c.symm w) hw.2
      simpa only [c.right_inv hw.1] using hh
    have hh := hdist b hb (c.symm w) hw.2 (f.symm w) (f.map_target hwt)
      (show (Φ (τ,(c b,f.symm w))).1 = c (c.symm w) by
        rw [c.right_inv hw.1]
        exact (congrFun hf _).symm.trans (f.right_inv hwt))
    have hn : 0 ≤ g (c b) (f.symm w) (f.symm w) := by
      by_cases hh : f.symm w = 0
      · simp only [hh,map_zero,le_refl]
      · exact (riemannianCoordinateMetric_positive (c.map_source (hsrc hb)) hh).le
    rw [hh,mul_pow,Real.sq_sqrt hn]
    ring
  let z := χ.symm (c b,v)
  have hzt : (c b,v) ∈ χ.target := (tangent_chart_target_iff A _).mpr (c.map_source (hsrc hb))
  have hzchart : χ z = (c b,v) := χ.right_inv hzt
  have hzsrc : z ∈ χ.source := χ.map_target hzt
  have hzb : z.1 = b := by
    have hh := congrArg Prod.fst hzchart
    rw [tangent_chart_apply] at hh
    exact c.injOn ((tangent_chart_source_iff A z).mp hzsrc) (hsrc hb) hh
  have hflow := sprayFlow_eq_coordinate_curve A hr
    (fun t ht' => (hode t ht' (c b,v) (hball v hv)).1)
    (fun t ht' => (hode t ht' (c b,v) (hball v hv)).2)
    (show χ.symm (Φ (0,(c b,v))) = z by rw [hΦ0 (c b,v) (hball v hv)]) ht
  have hflowchart : χ (sprayFlow τ z) = Φ (τ,(c b,v)) := by
    rw [hflow,χ.right_inv ((tangent_chart_target_iff A _).mpr (hode τ ht (c b,v) (hball v hv)).1)]
  have hflowsrc : sprayFlow τ z ∈ χ.source := by
    rw [hflow]
    exact χ.map_target ((tangent_chart_target_iff A _).mpr (hode τ ht (c b,v) (hball v hv)).1)
  have hfy : (sprayFlow τ z).1 = y := by
    apply c.injOn ((tangent_chart_source_iff A _).mp hflowsrc) (hsrc hy)
    exact (congrArg Prod.fst (tangent_chart_apply A (sprayFlow τ z))).symm.trans
      ((congrArg Prod.fst hflowchart).trans hΨv)
  refine ⟨z,hzb,hfy,?_,?_⟩
  · have hh := hdist b hb y hy v hvs hΨv
    have hn := coordinate_spray_energy A z ((tangent_chart_source_iff A z).mp hzsrc)
    rw [hzchart] at hn
    rw [hh,hn,Real.sqrt_sq (norm_nonneg _)]
  · have hh := hD.congr_of_eventuallyEq hdistEq
    rw [show (χ (sprayFlow τ z)).2 = W (τ,v) from congrArg Prod.snd hflowchart]
    exact hh

end WeakMTWTransport

end

end OAI
