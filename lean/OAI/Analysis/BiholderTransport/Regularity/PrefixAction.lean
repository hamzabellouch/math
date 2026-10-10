import Mathlib
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

def prefixAction (x : M) (t : ℝ)
    (q : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  cost (riemannianExp x q.1) (riemannianExp x (t • q.2))/t

lemma prefixAction_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x) :
    ContDiffAt ℝ ∞ (prefixAction x t) (0,p) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have he := contMDiff_riemannianExp_fiber (n := n) x
  have hu : ContMDiffAt 𝓘(ℝ,V×V) 𝓘(ℝ,Model n) ∞
      (fun q : V×V => riemannianExp x q.1) (0,p) :=
    (he _).comp (0,p) contDiffAt_fst.contMDiffAt
  have hv : ContMDiffAt 𝓘(ℝ,V×V) 𝓘(ℝ,Model n) ∞
      (fun q : V×V => riemannianExp x (t • q.2)) (0,p) :=
    (he _).comp (0,p) (show ContDiffAt ℝ ∞ (fun q : V×V => t • q.2) (0,p) from by fun_prop).contMDiffAt
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨x,t • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp
  have hc' : ContMDiffAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) 𝓘(ℝ,ℝ) ∞
      (fun q : M×M => cost q.1 q.2) (riemannianExp x (0:V),riemannianExp x (t • p)) := by
    simpa only [riemannianExp_zero] using hc
  exact ((hc'.comp (0,p) (hu.prodMk hv)).contDiffAt.div_const t)

lemma prefixAction_axis {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x) :
    prefixAction x t (0,p)=t*(‖p‖^2/2) := by
  have hm := injectivityDomain_subset_minimizingVectors x hp
  change dist x (riemannianExp x (t • p))=‖t • p‖ at hm
  simp only [prefixAction,riemannianExp_zero,cost,hm,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs]
  by_cases ht : t=0
  · simp [ht]
  · field_simp

lemma prefixAction_axis_near {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (hp : t • p ∈ injectivityDomain x) :
    (fun v => prefixAction x t (0,v)) =ᶠ[𝓝 p] (fun v => t*(‖v‖^2/2)) := by
  have hn : ∀ᶠ v : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 p, t • v ∈ injectivityDomain x :=
    (continuous_const_smul t).continuousAt.eventually ((isOpen_injectivityDomain x).mem_nhds hp)
  filter_upwards [hn] with v hv
  exact prefixAction_axis hv

lemma prefixAction_source_gradient {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : t≠0) (hp : t • p ∈ injectivityDomain x)
    (a : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (prefixAction x t) (0,p) (a,0) = -inner ℝ p a := by
  have hnc := ((normalCost_contDiffAt hp).differentiableAt (by simp)).hasFDerivAt
  have H := hnc.mul_const t⁻¹
  have hp₀ := (hasFDerivAt_id (𝕜 := ℝ) (0 : TangentSpace 𝓘(ℝ,Model n) x)).prodMk
    (hasFDerivAt_const p (0 : TangentSpace 𝓘(ℝ,Model n) x))
  have H' : HasFDerivAt (fun u => prefixAction x t (u,p))
      (t⁻¹ • fderiv ℝ (normalCost x (t • p)) 0) 0 := by
    simpa only [prefixAction,normalCost,div_eq_mul_inv] using H
  have hB := (prefixAction_contDiffAt hp).differentiableAt (by simp)
  have heq := (hB.hasFDerivAt.comp (f := fun u => (u,p)) 0 hp₀).unique H'
  have hh := congrArg (fun A : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => A a) heq
  change fderiv ℝ (prefixAction x t) (0,p) (a,0) =
    t⁻¹ * fderiv ℝ (normalCost x (t • p)) 0 a at hh
  rw [normalCost_fderiv_zero hp,real_inner_smul_left] at hh
  rw [hh]
  field_simp

lemma prefixAction_mixed {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {t : ℝ} (ht : t≠0) (hp : t • p ∈ injectivityDomain x)
    (a d : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (prefixAction x t)) (0,p) (0,d) (a,0) = -inner ℝ d a := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  have hC := (prefixAction_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hL : HasFDerivAt (fun v : V => ((0:V),v))
      ((0 : V →L[ℝ] V).prod (ContinuousLinearMap.id ℝ V)) p :=
    (hasFDerivAt_const (0:V) p).prodMk (hasFDerivAt_id (𝕜 := ℝ) p)
  have hd := (((hC.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp (f := fun v : V => ((0:V),v)) p hL).clm_apply
      (hasFDerivAt_const (a,(0:V)) p)
  have heq : (fun v : V => fderiv ℝ (prefixAction x t) (0,v) (a,0)) =ᶠ[𝓝 p]
      (fun v => -inner ℝ v a) := by
    have hn := (continuous_const_smul t).continuousAt.eventually
      ((isOpen_injectivityDomain x).mem_nhds hp)
    filter_upwards [hn] with v hv
    exact prefixAction_source_gradient ht hv a
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
