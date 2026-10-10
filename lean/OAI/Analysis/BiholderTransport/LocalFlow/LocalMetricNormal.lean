import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.CoordinateMetricNorm
import OAI.Analysis.BiholderTransport.Volume.RiemannianCalibration

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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

omit [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma coordinate_flow_path_length
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S) (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < g x v v)
    (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
    {c : M} (hSto : S ⊆ (extChartAt 𝓘(ℝ,E) c).target)
    (hmetric : ∀ z ∈ S, ∀ u v : E, g z u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) c).symm z) u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) c).symm z) v))
    {η V : ℝ → E} {r : ℝ} (hη : ContDiffOn ℝ ∞ η (Ioo (-r) r))
    (himg : MapsTo η (Ioo (-r) r) S)
    (hode : ∀ t ∈ Ioo (-r) r, HasDerivAt η (V t) t ∧
      HasDerivAt V (-coordinateChristoffel g (η t) (V t) (V t)) t)
    {τ : ℝ} (hτ : 0 ≤ τ) (hτr : τ < r) :
    pathELength 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) c).symm ∘ η) 0 τ =
      ENNReal.ofReal (τ * Real.sqrt (g (η 0) (V 0) (V 0))) := by
  have hr : 0 < r := hτ.trans_lt hτr
  have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨by linarith,hr⟩
  have hsub : Icc 0 τ ⊆ Ioo (-r) r := fun t ht => ⟨by linarith [ht.1],ht.2.trans_lt hτr⟩
  rw [inverse_coordinate_path_length ((hη.mono hsub).of_le (by simp))
    (fun t ht => hSto (himg (hsub ht))) g (fun t ht => hmetric _ (himg (hsub ht)))]
  have hi : ∀ y ∈ S, (g y).IsInvertible := fun y hy => metricDual_isInvertible (g y) (hpos y hy)
  have hc : ∀ t ∈ Icc 0 τ, g (η t) (deriv η t) (deriv η t) = g (η 0) (V 0) (V 0) := by
    intro t ht
    rw [(hode t (hsub ht)).1.deriv]
    exact coordinate_geodesic_speed_constant
      (fun s hs => (hg.contDiffAt (hS.mem_nhds (himg hs))).differentiableAt (by simp))
      (fun s hs => hi _ (himg hs)) (fun s hs => hsym _ (himg hs)) hode (hsub ht) h0
  calc
    _ = ∫⁻ t in Icc (0:ℝ) τ, ENNReal.ofReal (Real.sqrt (g (η 0) (V 0) (V 0))) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp only
      rw [hc t ht]
    _ = _ := by rw [setLIntegral_const,Real.volume_Icc,sub_zero,ENNReal.ofReal_mul hτ,mul_comm]

lemma riemannian_normal_chart_dist_lower
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S) (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < g x v v)
    (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
    {c : M}
    (hmetric : ∀ z ∈ S, ∀ u v : E, g z u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) c).symm z) u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) c).symm z) v))
    {Ψ W : ℝ × E → E} {r : ℝ}
    (hΨ : ContDiffOn ℝ ∞ Ψ (Ioo (-r) r ×ˢ Metric.ball 0 r))
    (hW : ContDiffOn ℝ ∞ W (Ioo (-r) r ×ˢ Metric.ball 0 r))
    (himg : ∀ t ∈ Ioo (-r) r, ∀ v ∈ Metric.ball 0 r, Ψ (t,v) ∈ S)
    (hode : ∀ t ∈ Ioo (-r) r, ∀ v ∈ Metric.ball 0 r,
      HasDerivAt (fun q => Ψ (q,v)) (W (t,v)) t ∧
      HasDerivAt (fun q => W (q,v))
        (-coordinateChristoffel g (Ψ (t,v)) (W (t,v)) (W (t,v))) t)
    {x : E} (h0 : 0 ∈ Ioo (-r) r)
    (hΨ0 : ∀ v ∈ Metric.ball 0 r, Ψ (0,v) = x)
    (hW0 : ∀ v ∈ Metric.ball 0 r, W (0,v) = v)
    {τ : ℝ} (hτ : τ ∈ Ioo (-r) r) (hτnonneg : 0 ≤ τ)
    (e : OpenPartialHomeomorph E E) (hef : (e : E → E) = fun v => Ψ (τ,v))
    (hes : 0 ∈ e.source) (hesub : e.source ⊆ Metric.ball 0 r)
    (hed : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {a y : M} (he0 : e 0 = extChartAt 𝓘(ℝ,E) c a)
    {δ : ℝ} (hball : Metric.ball a δ ⊆
      (extChartAt 𝓘(ℝ,E) c).source ∩ (extChartAt 𝓘(ℝ,E) c) ⁻¹' e.target)
    (hdist : dist a y < δ) :
    τ * Real.sqrt (g x (e.symm (extChartAt 𝓘(ℝ,E) c y))
      (e.symm (extChartAt 𝓘(ℝ,E) c y))) ≤ dist a y := by
  apply riemannian_local_dist_lower_bound (I := 𝓘(ℝ,E)) hball hdist
  intro γ hγ hγ0 hγ1 hγimg
  let η : ℝ → E := (extChartAt 𝓘(ℝ,E) c) ∘ γ
  have hη : ContDiffOn ℝ 1 η (Icc 0 1) :=
    contMDiffOn_iff_contDiffOn.mp
      ((contMDiffOn_extChartAt (I := 𝓘(ℝ,E)) (n := 1) (x := c)).comp hγ (fun t ht => by
        change γ t ∈ (chartAt E c).source
        simpa only [extChartAt_source] using (hγimg ht).1))
  have hηimg : MapsTo η (Icc 0 1) e.target := fun t ht => (hγimg ht).2
  have hηS : ∀ t ∈ Icc 0 1, η t ∈ S := by
    intro t ht
    have hh := himg τ hτ (e.symm (η t)) (hesub (e.map_target (hηimg ht)))
    have hval := congrFun hef (e.symm (η t))
    rw [←hval,e.right_inv (hηimg ht)] at hh
    exact hh
  have hb := coordinate_normal_chart_radial_bound hS hg hpos hsym hΨ hW himg hode
    h0 hΨ0 hW0 hτ hτnonneg e hef hes hesub hed hei (by norm_num : (0:ℝ) ≤ 1)
    hη hηimg (by simp only [η,Function.comp_apply,hγ0,he0])
  have hlen := coordinate_path_length hγ (fun t ht => (hγimg ht).1) g (by
    intro t ht u v
    have hh := hmetric (η t) (hηS t ht) u v
    have hinner := congrArg (fun z : M =>
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ z u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ z v))
        ((extChartAt 𝓘(ℝ,E) c).left_inv (hγimg ht).1)
    exact hh.trans hinner)
  rw [hlen]
  simpa only [η,Function.comp_apply,hγ1] using hb

lemma riemannian_coordinate_normal_chart_dist
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S) (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < g x v v)
    (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
    {c : M} (hSto : S ⊆ (extChartAt 𝓘(ℝ,E) c).target)
    (hmetric : ∀ z ∈ S, ∀ u v : E, g z u v =
      inner ℝ ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) c).symm z) u)
        ((trivializationAt E (fun x : M => TangentSpace 𝓘(ℝ,E) x) c).symmL ℝ
        ((extChartAt 𝓘(ℝ,E) c).symm z) v))
    {Ψ W : ℝ × E → E} {r : ℝ}
    (hΨ : ContDiffOn ℝ ∞ Ψ (Ioo (-r) r ×ˢ Metric.ball 0 r))
    (hW : ContDiffOn ℝ ∞ W (Ioo (-r) r ×ˢ Metric.ball 0 r))
    (himg : ∀ t ∈ Ioo (-r) r, ∀ v ∈ Metric.ball 0 r, Ψ (t,v) ∈ S)
    (hode : ∀ t ∈ Ioo (-r) r, ∀ v ∈ Metric.ball 0 r,
      HasDerivAt (fun q => Ψ (q,v)) (W (t,v)) t ∧
      HasDerivAt (fun q => W (q,v))
        (-coordinateChristoffel g (Ψ (t,v)) (W (t,v)) (W (t,v))) t)
    {a y : M} (h0 : 0 ∈ Ioo (-r) r)
    (hΨ0 : ∀ v ∈ Metric.ball 0 r, Ψ (0,v) = extChartAt 𝓘(ℝ,E) c a)
    (hW0 : ∀ v ∈ Metric.ball 0 r, W (0,v) = v)
    {τ : ℝ} (hτ : τ ∈ Ioo (-r) r) (hτnonneg : 0 ≤ τ)
    (e : OpenPartialHomeomorph E E) (hef : (e : E → E) = fun v => Ψ (τ,v))
    (he0 : e 0 = extChartAt 𝓘(ℝ,E) c a)
    (hes : 0 ∈ e.source) (hesub : e.source ⊆ Metric.ball 0 r)
    (hed : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {δ : ℝ} (hball : Metric.ball a δ ⊆
      (extChartAt 𝓘(ℝ,E) c).source ∩ (extChartAt 𝓘(ℝ,E) c) ⁻¹' e.target)
    (hdist : dist a y < δ) :
    dist a y = τ * Real.sqrt (g (extChartAt 𝓘(ℝ,E) c a)
      (e.symm (extChartAt 𝓘(ℝ,E) c y)) (e.symm (extChartAt 𝓘(ℝ,E) c y))) := by
  apply le_antisymm _ (riemannian_normal_chart_dist_lower hS hg hpos hsym hmetric
    hΨ hW himg hode h0 hΨ0 hW0 hτ hτnonneg e hef hes hesub hed hei he0 hball hdist)
  have hδ : 0 < δ := dist_nonneg.trans_lt hdist
  have ha := hball (Metric.mem_ball_self hδ)
  have hy := hball (show y ∈ Metric.ball a δ by simpa only [Metric.mem_ball,dist_comm] using hdist)
  let v := e.symm (extChartAt 𝓘(ℝ,E) c y)
  have hv : v ∈ Metric.ball 0 r := hesub (e.map_target hy.2)
  let η : ℝ → E := fun t => Ψ (t,v)
  have hη : ContDiffOn ℝ ∞ η (Ioo (-r) r) :=
    hΨ.comp (contDiffOn_id.prodMk contDiffOn_const) (fun t ht => ⟨ht,hv⟩)
  have hsub : Icc 0 τ ⊆ Ioo (-r) r := fun t ht => ⟨h0.1.trans_le ht.1,ht.2.trans_lt hτ.2⟩
  have hγ : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) 1
      ((extChartAt 𝓘(ℝ,E) c).symm ∘ η) (Icc 0 τ) :=
    (contMDiffOn_extChartAt_symm (n := 1) c).comp
      (contMDiffOn_iff_contDiffOn.mpr ((hη.mono hsub).of_le (by simp)))
      (fun t ht => hSto (himg t (hsub ht) v hv))
  have hγ0 : ((extChartAt 𝓘(ℝ,E) c).symm ∘ η) 0 = a := by
    simp only [Function.comp_apply,η,hΨ0 v hv,(extChartAt 𝓘(ℝ,E) c).left_inv ha.1]
  have hγτ : ((extChartAt 𝓘(ℝ,E) c).symm ∘ η) τ = y := by
    have heq := congrFun hef v
    simp only [Function.comp_apply,η,←heq,v,e.right_inv hy.2,
      (extChartAt 𝓘(ℝ,E) c).left_inv hy.1]
  have hh := riemannianEDist_le_pathELength (I := 𝓘(ℝ,E)) hγ hγ0 hγτ hτnonneg
  rw [←IsRiemannianManifold.out,edist_dist] at hh
  have hlen := coordinate_flow_path_length hS hg hpos hsym hSto hmetric hη
    (fun t ht => himg t ht v hv) (fun t ht => hode t ht v hv) hτnonneg hτ.2
  rw [hlen] at hh
  have hc : 0 ≤ τ * Real.sqrt (g (extChartAt 𝓘(ℝ,E) c a) v v) := mul_nonneg hτnonneg (Real.sqrt_nonneg _)
  have hh' : ENNReal.ofReal (dist a y) ≤
      ENNReal.ofReal (τ * Real.sqrt (g (extChartAt 𝓘(ℝ,E) c a) v v)) := by
    simpa only [η,hΨ0 v hv,hW0 v hv] using hh
  exact (ENNReal.ofReal_le_ofReal_iff hc).mp hh'

variable [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E
  (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
end WeakMTWTransport

end

end OAI
