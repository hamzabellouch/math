import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.LowerTaylor
import OAI.Analysis.BiholderTransport.LinearAlgebra.SplitEndpointJets
import OAI.Analysis.BiholderTransport.LinearAlgebra.PrefixActionJets

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma HasSecondTaylor.const_mul' {f : E → ℝ} {l : E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasSecondTaylor f l B) (c:ℝ) :
    HasSecondTaylor (fun h => c*f h) (c • l) (c • B) := by
  unfold HasSecondTaylor at *
  have he : (fun h => c*f h-c*f 0-(c • l) h-(c • B) h h/2) =
      (fun h => c*(f h-f 0-l h-B h h/2)) := by
    funext h; simp only [smul_apply,smul_eq_mul]; ring
  rw [he]
  exact hf.const_mul_left c

lemma HasSecondTaylor.sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ}
    {l : ι → E →L[ℝ] ℝ} {B : ι → E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ∀ i∈s, HasSecondTaylor (f i) (l i) (B i)) :
    HasSecondTaylor (fun h => ∑ i∈s, f i h) (∑ i∈s, l i) (∑ i∈s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    simp only [HasSecondTaylor,sub_self,zero_apply,zero_div]
    exact Asymptotics.isLittleO_zero _ _
  | @insert i s hi IH =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (IH (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma HasLowerSecondTaylor.mono_diagonal {f : E → ℝ} {l : E →L[ℝ] ℝ}
    {B C : E →L[ℝ] E →L[ℝ] ℝ} (hf : HasLowerSecondTaylor f l B)
    (hBC : ∀ h:E, C h h≤B h h) : HasLowerSecondTaylor f l C := by
  intro ε hε
  filter_upwards [hf ε hε] with h hh
  have H := hBC h
  linarith

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def prefixDefect (x : M) (t : ℝ) (p : TangentSpace 𝓘(ℝ,Model n) x)
    (h : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  prefixAction x t (h.1,p+h.2)-t*(‖p+h.2‖^2/2)

def splitDefect (x : M) (s : ℝ) (p : TangentSpace 𝓘(ℝ,Model n) x)
    (h : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) : ℝ :=
  splitEndpointCost x s (h.1,p+h.2)-‖p+h.2‖^2/2

lemma prefixDefect_taylor {x : M} {t : ℝ} (ht : t≠0)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : t • p∈injectivityDomain x) :
    ∃ B : (TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ]
      (TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ,
      HasSecondTaylor (prefixDefect x t p)
        ((-innerSL ℝ p).comp (ContinuousLinearMap.fst ℝ _ _)) B ∧
      ∀ a d : TangentSpace 𝓘(ℝ,Model n) x,
        B (a,d) (a,d)=hessianValue x (t • p) a/t-2*inner ℝ a d := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let P : V×V →L[ℝ] V := ContinuousLinearMap.snd ℝ V V
  let H : V×V →L[ℝ] V×V →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ (prefixAction x t)) (0,p)
  let D : V×V →L[ℝ] V×V →L[ℝ] ℝ := H-t • pullBilinear (innerSL ℝ) P
  have hC := (prefixAction_contDiffAt hp).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have HN : HasSecondTaylor (fun h:V×V => t*(‖p+P h‖^2/2))
      (t • ((innerSL ℝ p).comp P)) (t • pullBilinear (innerSL ℝ) P) :=
    ((norm_square_hasSecondTaylor p).comp_linear P).const_mul' t
  have HT := (hasSecondTaylor_shift hC).sub HN
  have hlin : fderiv ℝ (prefixAction x t) (0,p)-t • ((innerSL ℝ p).comp P)=
      (-innerSL ℝ p).comp (ContinuousLinearMap.fst ℝ V V) := by
    apply ContinuousLinearMap.ext
    rintro ⟨a,d⟩
    change fderiv ℝ (prefixAction x t) (0,p) (a,d)-t*inner ℝ p d = -inner ℝ p a
    rw [show (a,d)=((a,0):V×V)+(0,d) by simp,map_add,
      prefixAction_source_gradient ht hp,prefixAction_endpoint_gradient hp]
    ring
  rw [hlin] at HT
  refine ⟨D,?_,?_⟩
  · convert! HT using 1
    funext h
    rcases h with ⟨a,d⟩
    simp only [prefixDefect,Prod.mk_add_mk,zero_add,P,ContinuousLinearMap.coe_snd']
  · intro a d
    change fderiv ℝ (fderiv ℝ (prefixAction x t)) (0,p) (a,d) (a,d)-t*inner ℝ d d=_
    rw [prefixAction_hessian_diag ht hp,real_inner_self_eq_norm_sq]
    ring

lemma splitDefect_taylor {x : M} {s : ℝ} (hs : 0<s) (hs1 : s<1)
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : s • p∈injectivityDomain x)
    (hright : (1-s) • (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1) :
    ∃ B : (TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ]
      (TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x) →L[ℝ] ℝ,
      HasSecondTaylor (splitDefect x s p)
        ((-innerSL ℝ p).comp (ContinuousLinearMap.fst ℝ _ _)) B ∧
      ∀ a d : TangentSpace 𝓘(ℝ,Model n) x,
        B (a,d) (a,d)=hessianValue x (s • p) a/s-2*inner ℝ a d := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let P : V×V →L[ℝ] V := ContinuousLinearMap.snd ℝ V V
  let H := fderiv ℝ (fderiv ℝ (splitEndpointCost x s)) (0,p)
  let D := H-pullBilinear (innerSL ℝ) P
  have hC := (splitEndpointCost_contDiffAt hp hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have HT := (hasSecondTaylor_shift hC).sub
    ((norm_square_hasSecondTaylor p).comp_linear P)
  have hlin : fderiv ℝ (splitEndpointCost x s) (0,p)-((innerSL ℝ p).comp P)=
      (-innerSL ℝ p).comp (ContinuousLinearMap.fst ℝ V V) := by
    apply ContinuousLinearMap.ext
    rintro ⟨a,d⟩
    change fderiv ℝ (splitEndpointCost x s) (0,p) (a,d)-inner ℝ p d = -inner ℝ p a
    rw [show (a,d)=((a,0):V×V)+(0,d) by simp,map_add,
      splitEndpointCost_source_gradient hs.ne' hp hright,
      splitEndpointCost_endpoint_gradient hs hs1 hp hright]
    ring
  rw [hlin] at HT
  refine ⟨D,?_,?_⟩
  · convert! HT using 1
    funext h
    rcases h with ⟨a,d⟩
    simp only [splitDefect,Prod.mk_add_mk,zero_add,P,ContinuousLinearMap.coe_snd']
  · intro a d
    change fderiv ℝ (fderiv ℝ (splitEndpointCost x s)) (0,p) (a,d) (a,d)-inner ℝ d d=_
    rw [splitEndpointCost_hessian_diag hs hs1 hp hright,real_inner_self_eq_norm_sq]
    ring

end WeakMTWTransport

end

end OAI
