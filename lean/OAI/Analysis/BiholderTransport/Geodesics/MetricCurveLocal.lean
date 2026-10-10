import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.MetricCurveSpeed
import OAI.Analysis.BiholderTransport.Geodesics.GeodesicExistence
import OAI.Analysis.BiholderTransport.Coordinates.NormalRigidity

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

lemma metric_curve_eq_spray_local {γ : ℝ → M} {t k ε : ℝ}
    (hγ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ γ) (hε : 0 < ε)
    (hd : ∀ s u : ℝ, |s-t| < ε → |u-t| < ε → dist (γ s) (γ u) = |s-u| * k) :
    γ =ᶠ[𝓝 t] (fun s =>
      (sprayFlow (s-t) ⟨γ t,mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t (1:ℝ)⟩).1) := by
  let a := γ t
  let c := extChartAt 𝓘(ℝ,E) a
  let q := c ∘ γ
  let g := riemannianCoordinateMetric (E := E) a
  obtain ⟨δ,r,τ,hδ,hr,hτ,hτr,Ψ,W,e,hΨ,hW,hinit,hode,hef,hes,he0,hesub,
    hed,hei,hball,hdist,hD⟩ := exists_metric_normal_flow (E := E) a
  have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨by linarith,hr⟩
  have htau : τ ∈ Ioo (-r) r := ⟨by linarith,hτr⟩
  have hnear : γ ⁻¹' Metric.ball a δ ∩ Metric.ball t ε ∈ 𝓝 t :=
    inter_mem (hγ.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds a hδ))
      (Metric.ball_mem_nhds t hε)
  obtain ⟨η,hη,hsub⟩ := Metric.mem_nhds_iff.mp hnear
  let J := Ioo (t-η) (t+η)
  have hJ : ∀ s ∈ J, |s-t| < η := by intro s hs; exact abs_lt.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hJt : t ∈ J := ⟨by linarith,by linarith⟩
  have hclose : ∀ s ∈ J, γ s ∈ Metric.ball a δ ∧ |s-t| < ε := by
    intro s hs
    have H := hsub (show s ∈ Metric.ball t η by simpa only [Metric.mem_ball,Real.dist_eq] using hJ s hs)
    exact ⟨H.1,by simpa only [Metric.mem_ball,Real.dist_eq] using H.2⟩
  have hqsrc : ∀ s ∈ J, γ s ∈ c.source := fun s hs => (hball (hclose s hs).1).1
  have hqt : ∀ s ∈ J, q s ∈ e.target := fun s hs => (hball (hclose s hs).1).2
  have hq : ∀ s ∈ J, ContDiffAt ℝ ∞ q s := by
    intro s hs
    exact ((contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (x := a) (by simpa only [c,extChartAt_source] using hqsrc s hs)).comp s hγ.contMDiffAt).contDiffAt
  let f : ℝ → E := e.symm ∘ q
  have hf : ∀ s ∈ J, ContDiffAt ℝ ∞ f s := by
    intro s hs
    exact (hei.contDiffAt (e.open_target.mem_nhds (hqt s hs))).comp s (hq s hs)
  have hfs : MapsTo f J e.source := fun s hs => e.map_target (hqt s hs)
  have hf0 : f t = 0 := by change e.symm (c a) = 0; rw [←he0]; exact e.left_inv hes
  have heq : ∀ s ∈ J, e (f s) = q s := fun s hs => e.right_inv (hqt s hs)
  have heqnear : ∀ s ∈ J, (e ∘ f) =ᶠ[𝓝 s] q := by
    intro s hs
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact heq u hu
  have hsquares : ∀ s ∈ J, τ^2*g (c a) (f s) (f s) = (s-t)^2*k^2 := by
    intro s hs
    calc
      _ = (τ*Real.sqrt (g (c a) (f s) (f s)))^2 := by
        rw [mul_pow,Real.sq_sqrt (positive_bilinear_nonneg _
          (fun v hv => riemannianCoordinateMetric_positive (mem_extChartAt_target a) hv) _)]
      _ = dist (γ t) (γ s)^2 := by rw [hdist (γ s) (hclose s hs).1]; rfl
      _ = _ := by rw [hd t s (by simpa only [sub_self,abs_zero] using hε) (hclose s hs).2,
        mul_pow,sq_abs]; ring
  have hlin : ∀ s ∈ J, f s = (s-t) • deriv f t := by
    apply normal_chart_radial_rigidity e hed hei (g (c a))
      (riemannianCoordinateMetric_symm a (c a)) g (fun v => W (τ,v)) τ k
      (fun v hv w hw => riemannianCoordinateMetric_positive (by rw [hef]; exact (hode τ htau v (hesub hv)).1) hw)
      (fun v _ => riemannianCoordinateMetric_symm a (e v)) ?_ ?_ ?_
      (fun s hs => (hf s hs).contDiffWithinAt) hJt hfs ?_ hsquares
    · intro v hv
      have H := coordinate_geodesic_speed_constant
        (fun s hs => ((contDiffOn_riemannianCoordinateMetric a).contDiffAt
          ((isOpen_extChartAt_target a).mem_nhds (hode s hs v (hesub hv)).1)).differentiableAt (by simp))
        (fun s hs => riemannianCoordinateMetric_isInvertible (hode s hs v (hesub hv)).1)
        (fun s _ => riemannianCoordinateMetric_symm a (Ψ (s,v)))
        (fun s hs => (hode s hs v (hesub hv)).2) htau h0
      simpa only [hef,(hinit v (hesub hv)).1,(hinit v (hesub hv)).2] using H
    · intro v hv w
      have H := coordinate_endpoint_gauss (isOpen_extChartAt_target a)
        (contDiffOn_riemannianCoordinateMetric a)
        (fun x hx => riemannianCoordinateMetric_isInvertible hx)
        (fun x _ => riemannianCoordinateMetric_symm a x) hΨ hW
        (fun s hs v hv => (hode s hs v hv).1) (fun s hs v hv => (hode s hs v hv).2)
        h0 (fun v hv => (hinit v hv).1) (fun v hv => (hinit v hv).2) htau (hesub hv) w
      simpa only [hef] using H
    · intro v hv
      rw [hef]
      exact coordinate_endpoint_radial a hr hΨ hinit hode (hesub hv) htau
    · intro s hs
      rw [heq s hs,(heqnear s hs).deriv_eq]
      have Hspeed : g (q s) (deriv q s) (deriv q s) =
          ‖mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ s (1:ℝ)‖^2 :=
        coordinate_curve_speed_square (hγ.mdifferentiable (by simp) s) (hqsrc s hs)
      rw [Hspeed]
      apply metric_curve_speed_square hγ.contMDiffAt
      filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
      rw [hd s u (hclose s hs).2 (hclose u hu).2,abs_sub_comm s u]
  have hqtder : deriv q t = τ • deriv f t := by
    have heD := (hed.contDiffAt (e.open_source.mem_nhds hes)).differentiableAt (by simp)
    have hD' : HasFDerivAt e (τ • ContinuousLinearMap.id ℝ E) (f t) := by
      rw [hf0,←hD]; exact heD.hasFDerivAt
    have H := hD'.comp_hasDerivAt t ((hf t hJt).differentiableAt (by simp)).hasDerivAt
    simpa only [smul_apply,ContinuousLinearMap.id_apply] using
      (H.congr_of_eventuallyEq (heqnear t hJt).symm).deriv
  have hvel : τ • deriv f t = mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t (1:ℝ) :=
    hqtder.symm.trans (coordinate_curve_derivative_at_center (hγ.mdifferentiable (by simp) t))
  filter_upwards [isOpen_Ioo.mem_nhds hJt] with s hs
  have H := sprayFlow_eq_coordinate_curve (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) hr
    (fun u hu => (hode u hu (f s) (hesub (hfs hs))).1)
    (fun u hu => (hode u hu (f s) (hesub (hfs hs))).2.1.prodMk
      (hode u hu (f s) (hesub (hfs hs))).2.2)
    (show (extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M)).symm
        (Ψ (0,f s),W (0,f s)) = ⟨a,f s⟩ by
      rw [(hinit (f s) (hesub (hfs hs))).1,(hinit (f s) (hesub (hfs hs))).2]
      exact tangent_chart_at_self_base_symm (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) (f s)) htau
  have Hb := congrArg (fun z : TangentBundle 𝓘(ℝ,E) M => z.1) H
  rw [tangent_chart_symm_base,←congrFun hef (f s),heq s hs] at Hb
  have hbase : γ s = (sprayFlow τ ⟨a,f s⟩).1 := by
    rw [Hb]; exact (c.left_inv (hqsrc s hs)).symm
  rw [hbase,hlin s hs,←hvel]
  rw [show (⟨a,(s-t) • deriv f t⟩ : TangentBundle 𝓘(ℝ,E) M) =
    tangentScale (s-t) ⟨a,deriv f t⟩ from rfl,sprayFlow_scale]
  rw [show (⟨γ t,τ • deriv f t⟩ : TangentBundle 𝓘(ℝ,E) M) =
    tangentScale τ ⟨a,deriv f t⟩ from rfl,sprayFlow_scale]
  change (sprayFlow ((s-t)*τ) ⟨a,deriv f t⟩).1 = (sprayFlow (τ*(s-t)) ⟨a,deriv f t⟩).1
  rw [mul_comm]

end WeakMTWTransport

end

end OAI
