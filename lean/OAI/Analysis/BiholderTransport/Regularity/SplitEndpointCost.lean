import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.SplitStationary
import OAI.Analysis.BiholderTransport.Coordinates.SplitPairing

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def splitEndpointCost (x : M) (s : ℝ)
    (q : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  splitNormalAction x s q.2 (q.1,q.2)

lemma splitEndpointCost_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ContDiffAt ℝ ∞ (splitEndpointCost x s) (0,p) := by
  exact (splitNormalAction_contDiffAt hleft hright).comp
    (f := fun q : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x =>
      (q.2,(q.1,q.2))) (0,p)
    (contDiffAt_snd.prodMk (contDiffAt_fst.prodMk contDiffAt_snd))

lemma splitEndpointCost_axis {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    splitEndpointCost x s (0,p)=‖p‖^2/2 := by
  have hm := injectivityDomain_subset_minimizingVectors x hleft
  have hn := injectivityDomain_subset_minimizingVectors _ hright
  change dist x (riemannianExp x (s • p))=‖s • p‖ at hm
  change dist (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1
    (riemannianExp _ ((1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2)) = _ at hn
  rw [shifted_exp_endpoint] at hn
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hs] at hm
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hs1),sprayFlow_speed] at hn
  simp only [splitEndpointCost,splitNormalAction,riemannianExp_zero,cost]
  rw [hm,riemannianExp_smul,hn]
  field_simp
  ring

lemma splitEndpointCost_axis_near {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    (fun v => splitEndpointCost x s (0,v)) =ᶠ[𝓝 p] (fun v => ‖v‖^2/2) := by
  filter_upwards [split_regular_legs_near hleft hright] with v hv
  exact splitEndpointCost_axis hs hs1 hv.1 hv.2

lemma splitEndpointCost_source_gradient {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hs : s ≠ 0) (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (a : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (splitEndpointCost x s) (0,p) (a,0) = -inner ℝ p a := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hC := (splitEndpointCost_contDiffAt hleft hright).differentiableAt (by simp)
  have hB := (splitNormalAction_contDiffAt hleft hright).comp (0,p)
    (contDiffAt_const.prodMk contDiffAt_id)
  have hL : HasFDerivAt (fun b : V => (b,p))
      ((ContinuousLinearMap.id ℝ V).prod 0) 0 :=
    (hasFDerivAt_id (𝕜 := ℝ) (0:V)).prodMk (hasFDerivAt_const p (0:V))
  have hc := hC.hasFDerivAt.comp (f := fun b : V => (b,p)) 0 hL
  have hb := (hB.differentiableAt (by simp)).hasFDerivAt.comp (f := fun b : V => (b,p)) 0 hL
  have he := congrArg (fun A : V →L[ℝ] ℝ => A a) (hc.unique hb)
  change fderiv ℝ (splitEndpointCost x s) (0,p) (a,0) =
    fderiv ℝ (splitNormalAction x s p) (0,p) (a,0) at he
  rw [he]
  exact splitNormalAction_source_gradient hs hleft (hB.differentiableAt (by simp)) a

lemma splitEndpointCost_mixed {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hs : s ≠ 0) (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (a d : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (splitEndpointCost x s)) (0,p) (0,d) (a,0) =
      -inner ℝ d a := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hC := (splitEndpointCost_contDiffAt hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hL : HasFDerivAt (fun v : V => ((0:V),v))
      ((0 : V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)) p :=
    (hasFDerivAt_const (0:V) p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hd := (((hC.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun v : V => ((0:V),v)) p hL).clm_apply
      (hasFDerivAt_const (a,(0:V)) p)
  have heq : (fun v : V => fderiv ℝ (splitEndpointCost x s) (0,v) (a,0)) =ᶠ[𝓝 p]
      (fun v => -inner ℝ v a) := by
    filter_upwards [split_regular_legs_near hleft hright] with v hv
    exact splitEndpointCost_source_gradient hs hv.1 hv.2 a
  have hi : HasFDerivAt (fun v : V => -inner ℝ v a) (-(innerSL ℝ a)) p := by
    convert! ((innerSL ℝ a).hasFDerivAt (x := p)).neg using 1
    funext v; exact congrArg Neg.neg (real_inner_comm a v)
  have H := congrArg (fun A : V →L[ℝ] ℝ => A d)
    ((hd.congr_of_eventuallyEq heq.symm).unique hi)
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,zero_apply,map_zero,add_zero,zero_add,add_apply,
    ContinuousLinearMap.comp_zero,Function.comp_apply,
    ContinuousLinearMap.flip_apply,neg_apply,innerSL_apply_apply,real_inner_comm] using H

end WeakMTWTransport

end

end OAI
