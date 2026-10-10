import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.SplitActionSchur

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma second_fderiv_sub {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => f a-g a)) x v w =
      fderiv ℝ (fderiv ℝ f) x v w-fderiv ℝ (fderiv ℝ g) x v w := by
  have he : fderiv ℝ (fun a => f a-g a) =ᶠ[𝓝 x]
      (fun a => fderiv ℝ f a-fderiv ℝ g a) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with a ha hb
    exact fderiv_fun_sub (ha.differentiableAt (by norm_num)) (hb.differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  rw [fderiv_fun_sub ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))]
  rfl

lemma second_fderiv_const_mul {f : E → ℝ} {x : E} (c : ℝ) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => c*f a)) x v w = c*fderiv ℝ (fderiv ℝ f) x v w := by
  change fderiv ℝ (fderiv ℝ (c • f)) x v w = _
  rw [fderiv_const_smul_field c]
  rw [fderiv_const_smul_field (f := fderiv ℝ f) c]
  rfl

lemma second_fderiv_comp_stationary {f : F → ℝ} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x)
    (hzero : fderiv ℝ f (g x)=0) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => f (g a))) x v w =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) := by
  have hgd := (hg.differentiableAt (by norm_num)).hasFDerivAt
  have hd1 := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp (f := g) x hgd
  have hd2 := ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hd := hd1.clm_comp hd2
  have heq : (fun a => (fderiv ℝ f (g a)).comp (fderiv ℝ g a)) =ᶠ[𝓝 x]
      fderiv ℝ (fun a => f (g a)) := by
    filter_upwards [hgd.continuousAt.eventually (hf.eventually (by norm_num)),
      hg.eventually (by norm_num)] with a hfa hga
    exact ((hfa.differentiableAt (by norm_num)).hasFDerivAt.comp (f := g) a
      (hga.differentiableAt (by norm_num)).hasFDerivAt).fderiv.symm
  have H := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w)
    (hd.congr_of_eventuallyEq heq.symm).fderiv
  simpa only [Function.comp_apply,hzero,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.zero_comp,zero_apply,
    zero_add,add_zero,add_apply] using H

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def fixedJoinAction (x : M) (h T : ℝ) (p : TangentSpace 𝓘(ℝ,Model n) x)
    (z : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  cost (riemannianExp x z.1) (riemannianExp x (h • z.2))/h+
    cost (riemannianExp x (h • z.2)) (riemannianExp x (T • p))/(T-h)

def fixedJoinMiddle (x : M) (h T : ℝ) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ :=
  let I : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ]
      TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x :=
    (0 : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x).prod
      (ContinuousLinearMap.id ℝ _)
  ((fderiv ℝ (fderiv ℝ (fixedJoinAction x h T p)) (0,p)).comp I).flip.comp I |>.flip

section
omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

@[simp] lemma fixedJoinMiddle_apply (x : M) (h T : ℝ)
    (p d k : TangentSpace 𝓘(ℝ,Model n) x) :
    fixedJoinMiddle x h T p d k =
      fderiv ℝ (fderiv ℝ (fixedJoinAction x h T p)) (0,p) (0,d) (0,k) := rfl

lemma fixedJoinAction_rescale (x : M) {h T : ℝ} (hT : T≠0)
    (p : TangentSpace 𝓘(ℝ,Model n) x)
    (z : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) :
    fixedJoinAction x h T p z = T⁻¹*splitNormalAction x (h/T) (T • p) (z.1,T • z.2) := by
  simp only [fixedJoinAction,splitNormalAction,smul_smul,div_mul_cancel₀ _ hT]
  have he : 1-h/T=(T-h)/T := by field_simp
  rw [he]
  simp only [div_div_eq_mul_div]
  simp only [mul_add]
  congr 1 <;> field_simp [hT]

lemma fixedJoinMiddle_rescale {x : M} {h T : ℝ} (hT : T≠0)
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hB : ContDiffAt ℝ 2 (splitNormalAction x (h/T) (T • p)) (0,T • p))
    (d k : TangentSpace 𝓘(ℝ,Model n) x) :
    fixedJoinMiddle x h T p d k = T*
      fderiv ℝ (fderiv ℝ (splitNormalAction x (h/T) (T • p))) (0,T • p) (0,d) (0,k) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let L : V×V →L[ℝ] V×V := (ContinuousLinearMap.fst ℝ V V).prod
    (T • ContinuousLinearMap.snd ℝ V V)
  have he : fixedJoinAction x h T p=(fun z => T⁻¹*splitNormalAction x (h/T) (T • p) (L z)) :=
    funext (fixedJoinAction_rescale x hT p)
  rw [fixedJoinMiddle_apply,he,second_fderiv_const_mul]
  have HL := second_fderiv_comp_affine (f := splitNormalAction x (h/T) (T • p)) L 0 (0,p)
    (by simpa [L] using hB) (0,d) (0,k)
  simp only [zero_add] at HL
  rw [HL]
  change T⁻¹*fderiv ℝ (fderiv ℝ (splitNormalAction x (h/T) (T • p))) (0,T • p)
    (0,T • d) (0,T • k)=_
  have he1 (v : V) : ((0:V),T • v)=T • ((0:V),v) := by simp
  simp only [he1,map_smul,smul_apply,smul_eq_mul]
  field_simp [hT]

end

lemma fixedJoinAction_schur {x : M} {h T : ℝ}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : T • p∈injectivityDomain x) (hh : 0<h) (hhT : h<T) :
    ∃ R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
      (∀ d k, fixedJoinMiddle x h T p (R d) k=inner ℝ d k) ∧
      (∀ d, hessianValue x (T • p) d/T=hessianValue x (h • p) d/h-inner ℝ (R d) d) := by
  have hT : 0<T := hh.trans hhT
  have ht : 0<h/T := div_pos hh hT
  have ht1 : h/T<1 := (div_lt_one hT).mpr hhT
  obtain ⟨R,hR,hA⟩ := splitNormalAction_schur_equality hp ht ht1
  have hleft := contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors x hp) ht ht1
  have hright := shifted_injectivityDomain_of_injectivityDomain hp ht.le ht1
  have hBc := (splitNormalAction_contDiffAt hleft hright).comp
    (f := fun z : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x => (T • p,z))
    (0,T • p) (contDiffAt_const.prodMk contDiffAt_id)
  have hB := hBc.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  refine ⟨T⁻¹ • R,?_,?_⟩
  · intro d k
    rw [smul_apply,map_smul,smul_apply,
      fixedJoinMiddle_rescale hT.ne' hB,hR]
    simp [smul_eq_mul,hT.ne']
  · intro d
    have HA := hA d
    rw [smul_smul,div_mul_cancel₀ _ hT.ne'] at HA
    rw [HA,smul_apply,real_inner_smul_left]
    field_simp

end WeakMTWTransport

end

end OAI
