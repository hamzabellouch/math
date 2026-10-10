import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.LocalCostSmooth
import OAI.Analysis.BiholderTransport.Geodesics.SprayActionMinimum
import OAI.Analysis.BiholderTransport.Regularity.ActionLocalData
import OAI.Analysis.BiholderTransport.Coordinates.CoordinateGradient
import OAI.Analysis.BiholderTransport.Calculus.ActionCalculus

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

open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma sprayFlow_interior_nonconjugate (x : M) (p : TangentSpace 𝓘(ℝ,E) x)
    {t T : ℝ} (ht : 0<t) (hT : t<T)
    (hmin : dist x (sprayFlow T (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 = T*‖p‖) :
    Function.Injective (fderiv ℝ
      (fun v : TangentSpace 𝓘(ℝ,E) x => extChartAt 𝓘(ℝ,E)
        (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1
        (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1) p) := by
  let a := sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)
  let c := extChartAt 𝓘(ℝ,E) a.1
  let χ := extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) a
  let Q : TangentSpace 𝓘(ℝ,E) x → E := fun v => c (sprayFlow t ⟨x,v⟩).1
  let V : TangentSpace 𝓘(ℝ,E) x → E := fun v => (χ (sprayFlow t ⟨x,v⟩)).2
  let g := riemannianCoordinateMetric (E := E) a.1
  have hsrc : a.1 ∈ c.source := mem_extChartAt_source a.1
  have hQp : Q p = c a.1 := rfl
  have htarget : Q p ∈ c.target := by
    rw [hQp]
    exact c.map_source hsrc
  have hInv : c.symm (Q p)=a.1 := c.left_inv hsrc
  have hΦ : ContDiffAt ℝ ∞ (fun v : TangentSpace 𝓘(ℝ,E) x => χ (sprayFlow t ⟨x,v⟩)) p :=
    ((show ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E×E) ∞ χ a from
      contMDiffAt_extChartAt).comp p (contMDiff_spray_fiber x t p)).contDiffAt
  have hΦeq : (fun v : TangentSpace 𝓘(ℝ,E) x => χ (sprayFlow t ⟨x,v⟩)) = fun v => (Q v,V v) := by
    funext v
    apply Prod.ext
    · exact congrArg Prod.fst (tangent_chart_apply a (sprayFlow t ⟨x,v⟩))
    · rfl
  rw [hΦeq] at hΦ
  have hQ := hΦ.fst
  have hV := hΦ.snd
  obtain ⟨δ,hδ,hC⟩ := exists_local_cost_smooth (E := E) a.1
  obtain ⟨ε,hε,hεt,hεT,hy,hlocal⟩ := exists_two_short_legs x p ht hT hδ
  let L := t-ε
  let y := (sprayFlow (t+ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1
  let b : TangentSpace 𝓘(ℝ,E) x → M := fun v => (sprayFlow L ⟨x,v⟩).1
  let K : E → ℝ := fun q => (dist (c.symm q) y^2/2)/ε
  let B : TangentSpace 𝓘(ℝ,E) x × E → ℝ := fun z =>
    L*‖z.1‖^2/2 + (dist (b z.1) (c.symm z.2)^2/2)/ε + K z.2
  have hL : 0<L := sub_pos.mpr hεt
  have hlp := hlocal.self_of_nhds
  have hb : ContMDiff 𝓘(ℝ,TangentSpace 𝓘(ℝ,E) x) 𝓘(ℝ,E) ∞ b :=
    (Bundle.contMDiff_proj (fun z : M => TangentSpace 𝓘(ℝ,E) z)).comp (contMDiff_spray_fiber x L)
  have hqδ : c.symm (Q p) ∈ Metric.ball a.1 δ := by rw [hInv]; exact Metric.mem_ball_self hδ
  have hIC := coordinate_cost_contDiffAt hC (hb p) hlp.1 htarget hqδ
  have hK : ContDiffAt ℝ ∞ K (Q p) :=
    (coordinate_outgoing_cost_contDiffAt hC hy htarget hqδ).div_const ε
  have hB : ContDiffAt ℝ 2 B (p,Q p) := by
    have hn : ContDiffAt ℝ ∞ (fun z : TangentSpace 𝓘(ℝ,E) x × E => L*‖z.1‖^2/2) (p,Q p) :=
      (contDiffAt_const.mul ((contDiff_norm_sq ℝ).contDiffAt.comp (p,Q p) contDiffAt_fst)).div_const 2
    exact ((hn.add (hIC.div_const ε)).add (hK.comp (p,Q p) contDiffAt_snd)).of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hm : dist x (sprayFlow (L+2*ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 = (L+2*ε)*‖p‖ :=
    sprayFlow_minimizing_prefix (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)
      (by positivity) (by dsimp [L]; linarith) hmin
  have hBcontact : B (p,Q p)=(L+2*ε)*‖p‖^2/2 := by
    dsimp [B,K]
    rw [hInv]
    have heq₁ : L+ε=t := by dsimp [L]; ring
    have heq₂ : L+2*ε=t+ε := by dsimp [L]; ring
    convert! spray_split_action_contact x p hL hε hm using 1;
      simp only [heq₁,heq₂,div_div,b,y,a]
  have hBmin : IsLocalMin B (p,Q p) := by
    apply Filter.Eventually.of_forall
    intro z
    rw [hBcontact]
    have heq : L+2*ε=t+ε := by dsimp [L]; ring
    convert! spray_split_action_minimum x p hL hε hm z.1 (c.symm z.2) using 1;
      simp only [B,K,b,y,heq,div_div]
  have hnear : ∀ᶠ v : TangentSpace 𝓘(ℝ,E) x in 𝓝 p,
      (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1 ∈ c.source :=
    ((Bundle.contMDiff_proj (fun z : M => TangentSpace 𝓘(ℝ,E) z)).comp
      (contMDiff_spray_fiber x t) p).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source a.1).mem_nhds hsrc)
  have hBnear : ∀ᶠ v in 𝓝 p, DifferentiableAt ℝ B (v,Q v) :=
    (continuousAt_id.prodMk hQ.continuousAt).tendsto.eventually
      ((hB.eventually (by norm_num)).mono (fun _ h => h.differentiableAt (by norm_num)))
  have hKnear : ∀ᶠ v in 𝓝 p, DifferentiableAt ℝ K (Q v) :=
    hQ.continuousAt.tendsto.eventually
      (((hK.of_le (m := 1) (by simp)).eventually (by norm_num)).mono
        (fun _ h => h.differentiableAt (by norm_num)))
  have hstat : ∀ᶠ v in 𝓝 p, ∀ w : TangentSpace 𝓘(ℝ,E) x, fderiv ℝ B (v,Q v) (w,0)=0 := by
    filter_upwards [hlocal,hnear,hBnear] with v hv hvs hBd
    intro w
    apply fderiv_fst_eq_of_line_stationary hBd
    have hd := (spray_action_line_stationary x v w L ε hε.ne'
      (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1 hv.2.2.1).add_const (K (Q v))
    simpa only [B,b,Q,c.left_inv hvs,zero_add] using hd
  have hcot : ∀ᶠ v in 𝓝 p, ∀ u : E,
      fderiv ℝ B (v,Q v) (0,u) = g (Q v) (V v) u + fderiv ℝ K (Q v) u := by
    filter_upwards [hlocal,hnear,hBnear,hKnear] with v hv hvs hBd hKd
    intro u
    have hd := (coordinate_gradient_of_hasMFDerivAt
      (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)) hvs
      (fun q => dist (b v) q^2/2) ε hv.2.2.2).mul_const ε⁻¹
    have hI : HasFDerivAt (fun q : E => (dist (b v) (c.symm q)^2/2)/ε)
        (g (Q v) (V v)) (Q v) := by
      convert! hd using 1
      simp only [smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
      rfl
    have H := ((hasFDerivAt_const (L*‖v‖^2/2) (Q v)).add hI).add hKd.hasFDerivAt
    have H' : HasFDerivAt (fun q : E => B (v,q)) (g (Q v) (V v)+fderiv ℝ K (Q v)) (Q v) := by
      convert! H using 1
      ext z
      simp only [_root_.add_apply, zero_add]
    exact fderiv_snd_eq_of_partial hBd H' u
  have hg : DifferentiableAt ℝ g (Q p) :=
    ((contDiffOn_riemannianCoordinateMetric a.1).contDiffAt
      ((isOpen_extChartAt_target a.1).mem_nhds htarget)).differentiableAt (by simp)
  have hR : DifferentiableAt ℝ (fderiv ℝ K) (Q p) :=
    (hK.fderiv_right (m := 1) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).differentiableAt (by norm_num)
  have hpos : ∀ u : E, u≠0 → 0<g (Q p) u u :=
    fun _ hu => riemannianCoordinateMetric_positive htarget hu
  have himm : Function.Injective (fderiv ℝ (fun v => (Q v,V v)) p) := by
    rw [←hΦeq]
    exact coordinate_spray_fiber_immersion x p t
  exact generating_graph_position_immersion hB hBmin
    (hQ.differentiableAt (by simp)) (hV.differentiableAt (by simp)) hg hR hpos hstat hcot himm

end WeakMTWTransport

end

end OAI
