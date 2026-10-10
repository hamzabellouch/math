import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.JetPullback
import OAI.Analysis.BiholderTransport.Regularity.PrefixAction

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

lemma prefixAction_source_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x)
    (a : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixAction x t)) (0,p) (a,0) (a,0) =
      hessianValue x (t • p) a/t := by
  have hC := (prefixAction_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [←iteratedDeriv_two_affine_line hC (a,0)]
  simp only [prefixAction,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
    smul_zero,zero_add,add_zero]
  change iteratedDeriv 2 (fun r : ℝ =>
    cost (riemannianExp x (r • a)) (riemannianExp x (t • p))/t) 0 = _
  rw [iteratedDeriv_div_const]
  rfl

lemma prefixAction_endpoint_gradient {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x)
    (d : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (prefixAction x t) (0,p) (0,d) = t*inner ℝ p d := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hD := (prefixAction_contDiffAt hp).differentiableAt (by simp)
  have hL := (hasFDerivAt_const (0:V) p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have H := (hD.hasFDerivAt.comp (f := fun v : V => ((0:V),v)) p hL).congr_of_eventuallyEq
    (prefixAction_axis_near hp).symm
  have he := congrArg (fun A : V →L[ℝ] ℝ => A d)
    (H.unique ((half_norm_sq_hasFDerivAt p).const_smul t))
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    zero_apply,smul_apply,smul_eq_mul,innerSL_apply_apply] at he
  exact he

lemma prefixAction_endpoint_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x)
    (d e : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixAction x t)) (0,p) (0,d) (0,e) = t*inner ℝ d e := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hC := (prefixAction_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have he := ((prefixAction_axis_near hp).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  let L : V →L[ℝ] V×V := (0:V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)
  have H := second_fderiv_comp_affine L 0 p
    (by simpa only [L,ContinuousLinearMap.prod_apply,zero_apply,
      ContinuousLinearMap.id_apply,zero_add] using hC) d e
  simp only [L,ContinuousLinearMap.prod_apply,zero_apply,
    ContinuousLinearMap.id_apply,zero_add] at H
  rw [←H,he]
  have hg : fderiv ℝ (fun v : V => t*(‖v‖^2/2)) =
      (fun v => t • innerSL ℝ v) := by
    funext v
    exact ((half_norm_sq_hasFDerivAt v).const_smul t).fderiv
  rw [hg]
  have hD : HasFDerivAt (fun v : V => t • innerSL ℝ v) (t • innerSL ℝ) p := by
    convert! ((innerSL ℝ).hasFDerivAt (x := p)).const_smul t using 1
  rw [hD.fderiv]
  rfl

lemma prefixAction_hessian_diag {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : t≠0) (hp : t • p ∈ injectivityDomain x)
    (a d : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixAction x t)) (0,p) (a,d) (a,d) =
      hessianValue x (t • p) a/t-2*inner ℝ a d+t*‖d‖^2 := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hsplit : (a,d)=((a,0):V×V)+(0,d) := by simp
  have hsym := (prefixAction_contDiffAt hp).isSymmSndFDerivAt
    (by simp)
  rw [hsplit]
  simp only [map_add,add_apply]
  rw [prefixAction_source_hessian hp,hsym.eq (a,0) (0,d),
    prefixAction_mixed ht hp,prefixAction_endpoint_hessian hp]
  rw [real_inner_self_eq_norm_sq,real_inner_comm d a]
  ring

end WeakMTWTransport

end

end OAI
