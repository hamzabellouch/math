import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.SplitEndpointCost
import OAI.Analysis.BiholderTransport.Calculus.JetPullback

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

lemma splitEndpointCost_source_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (a : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (splitEndpointCost x s)) (0,p) (a,0) (a,0) =
      hessianValue x (s • p) a / s := by
  have hC := (splitEndpointCost_contDiffAt hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have H := iteratedDeriv_two_affine_line hC (a,0)
  rw [← H]
  have he : (fun r : ℝ => splitEndpointCost x s ((0,p)+r • (a,0))) =
      (fun r => cost (riemannianExp x (s • p)) (riemannianExp x p)/(1-s) +
        cost (riemannianExp x (r • a)) (riemannianExp x (s • p))/s) := by
    funext r
    simp only [splitEndpointCost, splitNormalAction, Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,smul_zero,zero_add,add_zero]
    exact add_comm _ _
  rw [he,iteratedDeriv_const_add (by norm_num : 0<2),iteratedDeriv_div_const]
  rfl

lemma splitEndpointCost_endpoint_gradient {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hs : 0<s) (hs1 : s<1)
    (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (d : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (splitEndpointCost x s) (0,p) (0,d) = inner ℝ p d := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hC := (splitEndpointCost_contDiffAt hleft hright).differentiableAt (by simp)
  have hL : HasFDerivAt (fun v : V => ((0:V),v))
      ((0 : V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)) p :=
    (hasFDerivAt_const (0:V) p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hd := (hC.hasFDerivAt.comp (f := fun v : V => ((0:V),v)) p hL).congr_of_eventuallyEq
    (splitEndpointCost_axis_near hs hs1 hleft hright).symm
  have he := congrArg (fun A : V →L[ℝ] ℝ => A d) (hd.unique (half_norm_sq_hasFDerivAt p))
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,zero_apply,
    ContinuousLinearMap.id_apply,innerSL_apply_apply] using he

lemma splitEndpointCost_endpoint_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hs : 0<s) (hs1 : s<1)
    (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (d e : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (splitEndpointCost x s)) (0,p) (0,d) (0,e) = inner ℝ d e := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let L : V →L[ℝ] V×V := (0 : V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)
  have hC := (splitEndpointCost_contDiffAt hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have heq := ((splitEndpointCost_axis_near hs hs1 hleft hright).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  have he := congrArg (fun A : V →L[ℝ] V →L[ℝ] ℝ => A d e) heq
  have H := second_fderiv_comp_affine L (0:V×V) p
    (by simpa only [L,ContinuousLinearMap.prod_apply,zero_apply,
      ContinuousLinearMap.id_apply,zero_add] using hC) d e
  simp only [L,ContinuousLinearMap.prod_apply,zero_apply,
    ContinuousLinearMap.id_apply,zero_add] at H
  rw [← H,he,half_norm_sq_second_fderiv]

lemma splitEndpointCost_hessian_diag {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {s : ℝ} (hs : 0<s) (hs1 : s<1)
    (hleft : s • p ∈ injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    (a d : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (splitEndpointCost x s)) (0,p) (a,d) (a,d) =
      hessianValue x (s • p) a / s - 2*inner ℝ a d + ‖d‖^2 := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hsplit : (a,d)=((a,0):V×V)+(0,d) := by simp
  have hsym := (splitEndpointCost_contDiffAt hleft hright).isSymmSndFDerivAt
    (by simp)
  rw [hsplit]
  simp only [map_add,add_apply]
  rw [splitEndpointCost_source_hessian hleft hright,
    hsym.eq (a,0) (0,d),
    splitEndpointCost_mixed hs.ne' hleft hright,
    splitEndpointCost_endpoint_hessian hs hs1 hleft hright]
  rw [real_inner_self_eq_norm_sq,real_inner_comm d a]
  ring

end WeakMTWTransport

end

end OAI
