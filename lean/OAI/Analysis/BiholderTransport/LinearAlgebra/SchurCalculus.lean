import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ProperPieces
import OAI.Analysis.BiholderTransport.Calculus.SecondDerivativeSlice
import OAI.Analysis.BiholderTransport.Regularity.SplitSelection

namespace OAI

section
section
noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section SchurCalculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma stationary_graph_hessian_identity {B : E×F → ℝ} {q : E → F} {p : E}
    (hB : ContDiffAt ℝ 2 B (p,q p)) (hq : DifferentiableAt ℝ q p)
    (hstat : ∀ᶠ a in 𝓝 p, ∀ k, fderiv ℝ B (a,q a) (0,k)=0)
    (v : E) (k : F) :
    fderiv ℝ (fderiv ℝ B) (p,q p) (0,fderiv ℝ q p v) (0,k)=
      -fderiv ℝ (fderiv ℝ B) (p,q p) (v,0) (0,k) := by
  have hdf := (hB.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG := (hasFDerivAt_id (𝕜 := ℝ) p).prodMk hq.hasFDerivAt
  have hD := ((hdf.hasFDerivAt.comp (f := fun a => (a,q a)) p hG).clm_apply
    (hasFDerivAt_const ((0:E),k) p)).fderiv
  have heq : (fun a => fderiv ℝ B (a,q a) (0,k)) =ᶠ[𝓝 p] (fun _ => (0:ℝ)) :=
    hstat.mono (fun _ h => h k)
  have hz : fderiv ℝ (fun a => fderiv ℝ B (a,q a) (0,k)) p=0 := by
    rw [heq.fderiv_eq]
    exact (hasFDerivAt_const (0:ℝ) p).fderiv
  have H := congrArg (fun A : E →L[ℝ] ℝ => A v) (hD.symm.trans hz)
  simp only [add_apply,comp_apply,zero_apply,map_zero,zero_add,
    flip_apply,prod_apply,id_apply] at H
  rw [show (v,fderiv ℝ q p v)=(v,0)+((0:E),fderiv ℝ q p v) by ext <;> simp,
    map_add,add_apply] at H
  linarith

lemma stationary_graph_envelope_fderiv {B : E×F → ℝ} {q : E → F} {p : E}
    (hB : DifferentiableAt ℝ B (p,q p)) (hq : DifferentiableAt ℝ q p)
    (hstat : ∀ k, fderiv ℝ B (p,q p) (0,k)=0) :
    HasFDerivAt (fun a => B (a,q a)) ((fderiv ℝ B (p,q p)).comp (inl ℝ E F)) p := by
  apply (hB.hasFDerivAt.comp (f := fun a => (a,q a)) p
    ((hasFDerivAt_id (𝕜 := ℝ) p).prodMk hq.hasFDerivAt)).congr_fderiv
  ext v
  simp only [comp_apply,prod_apply,id_apply,inl_apply]
  rw [show (v,fderiv ℝ q p v)=(v,0)+((0:E),fderiv ℝ q p v) by ext <;> simp,
    map_add,hstat,add_zero]

lemma stationary_graph_schur_hessian {B : E×F → ℝ} {q : E → F} {p : E}
    (hB : ContDiffAt ℝ 2 B (p,q p)) (hq : ContDiffAt ℝ 1 q p)
    (hstat : ∀ᶠ a in 𝓝 p, ∀ k, fderiv ℝ B (a,q a) (0,k)=0)
    (v w : E) :
    fderiv ℝ (fderiv ℝ (fun a => B (a,q a))) p v w=
      fderiv ℝ (fderiv ℝ B) (p,q p) (v,0) (w,0)-
      fderiv ℝ (fderiv ℝ B) (p,q p) (0,fderiv ℝ q p v) (0,fderiv ℝ q p w) := by
  have hdq := hq.differentiableAt (by norm_num)
  have hdf := (hB.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG := (hasFDerivAt_id (𝕜 := ℝ) p).prodMk hdq.hasFDerivAt
  have hBn := hG.continuousAt.eventually ((hB.of_le (m := 1) (by norm_num)).eventually (by norm_num))
  have hqn := hq.eventually (by norm_num)
  have heq : fderiv ℝ (fun a => B (a,q a)) =ᶠ[𝓝 p]
      (fun a => (fderiv ℝ B (a,q a)).comp (inl ℝ E F)) := by
    filter_upwards [hBn,hqn,hstat] with a ha hb hc
    exact (stationary_graph_envelope_fderiv (ha.differentiableAt (by norm_num))
      (hb.differentiableAt (by norm_num)) hc).fderiv
  have hD := (hdf.hasFDerivAt.comp (f := fun a => (a,q a)) p hG).clm_comp
    (hasFDerivAt_const (inl ℝ E F) p)
  have H := congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w)
    (heq.fderiv_eq.trans hD.fderiv)
  simp only [add_apply,comp_apply,zero_apply,map_zero,zero_add,
    flip_apply,prod_apply,id_apply,inl_apply,compL_apply] at H
  rw [show (v,fderiv ℝ q p v)=(v,0)+((0:E),fderiv ℝ q p v) by ext <;> simp,
    map_add,add_apply] at H
  have HS := stationary_graph_hessian_identity hB hdq hstat w (fderiv ℝ q p v)
  have hsym := (hB.isSymmSndFDerivAt (by norm_num)).eq
  rw [hsym (w,0) (0,fderiv ℝ q p v),
    hsym (0,fderiv ℝ q p w) (0,fderiv ℝ q p v)] at HS
  linarith

end SchurCalculus
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section SchurAction
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma fixedSplitAction_contDiffAt {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈minimizingVectors x) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    ContDiffAt ℝ ∞ (splitNormalAction x t p) (0,p) := by
  have hleft := contracted_minimizer_mem_injectivityDomain hp ht ht1
  have hright := proper_suffix_in_injectivityDomain
    (z := (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)) hp ht ht1 le_rfl
  exact (splitNormalAction_contDiffAt hleft hright).comp
    (f := fun q : TangentSpace 𝓘(ℝ,Model n) x × TangentSpace 𝓘(ℝ,Model n) x => (p,q)) (0,p)
    (contDiffAt_const.prodMk contDiffAt_id)

lemma fixedSplitAction_source_hessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈minimizingVectors x) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (v : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (splitNormalAction x t p)) (0,p) (v,0) (v,0)=
      normalHessian x (t • p) v v/t := by
  have hB := fixedSplitAction_contDiffAt hp ht ht1
  have H := iteratedDeriv_two_affine_line
    (hB.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (v,0)
  simp only [splitNormalAction,Prod.fst_add,Prod.smul_fst,Prod.snd_add,Prod.smul_snd,
    zero_add,smul_zero,add_zero] at H
  conv_lhs at H => arg 2; ext r; rw [add_comm]
  rw [iteratedDeriv_const_add (by norm_num : 0<(2:ℕ)),iteratedDeriv_div_const] at H
  rw [←H,←hessianValue_eq_normalHessian (contracted_minimizer_mem_injectivityDomain hp ht ht1)]
  rfl

lemma exists_splitAction_schur_operator {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    ∃ K : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
      Function.Bijective K ∧ (∀ v w, inner ℝ (K v) w=inner ℝ v (K w)) ∧
      (∀ v, 0≤ inner ℝ (K v) v) ∧
      (∀ v k, fderiv ℝ (fderiv ℝ (splitNormalAction x t p)) (0,p) (0,K v) (0,k)=inner ℝ k v) ∧
      ∀ v, normalHessian x p v v=normalHessian x (t • p) v v/t-inner ℝ (K v) v := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let : FiniteDimensional ℝ X := inferInstanceAs (FiniteDimensional ℝ (Model n))
  let B := splitNormalAction x t p
  have hpG := injectivityDomain_subset_minimizingVectors x hp
  have hSmooth := fixedSplitAction_contDiffAt hpG ht ht1
  have hB : ContDiffAt ℝ 2 B (0,p) :=
    hSmooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hleft := contracted_minimizer_mem_injectivityDomain hpG ht ht1
  have hright := proper_suffix_in_injectivityDomain
    (z := (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)) hpG ht ht1 le_rfl
  obtain ⟨a,ha0,ha,he⟩ := exists_split_minimizing_selection hp ht ht1
  have hG : ContinuousAt (fun u => (u,a u)) (0:X) := continuousAt_id.prodMk ha.continuousAt
  have hBn : ∀ᶠ u in 𝓝 (0:X), DifferentiableAt ℝ B (u,a u) := by
    apply (hG.eventually (show ∀ᶠ z in 𝓝 ((0:X),a 0), ContDiffAt ℝ 2 B z from by
      rw [ha0]; exact hB.eventually (by norm_num))).mono
    exact fun u hu => hu.differentiableAt (by norm_num)
  have hstat : ∀ᶠ u in 𝓝 (0:X), ∀ k, fderiv ℝ B (u,a u) (0,k)=0 := by
    filter_upwards [he,hBn] with u hu hbu
    have hmin : IsLocalMin (fun v => B (u,v)) (a u) := by
      filter_upwards [] with v
      change splitNormalAction x t p (u,a u)≤ splitNormalAction x t p (u,v)
      rw [hu]
      exact normalCost_le_splitNormalAction x p u v ht ht1
    have hD := hbu.hasFDerivAt.comp (f := fun v => (u,v)) (a u)
      ((hasFDerivAt_const u (a u)).prodMk (hasFDerivAt_id (𝕜 := ℝ) (a u)))
    have hz := hmin.hasFDerivAt_eq_zero hD
    intro k
    exact congrArg (fun L : X →L[ℝ] ℝ => L k) hz
  let K := fderiv ℝ a 0
  have hBa : ContDiffAt ℝ 2 B (0,a 0) := by rwa [ha0]
  have hInv (v k : X) : fderiv ℝ (fderiv ℝ B) (0,p) (0,K v) (0,k)=inner ℝ k v := by
    have H := stationary_graph_hessian_identity hBa (ha.differentiableAt (by simp)) hstat v k
    rw [ha0,splitNormalAction_mixed_pairing ht.ne' hleft hright] at H
    simpa only [neg_neg] using H
  have hKinj : Function.Injective K := by
    apply (injective_iff_map_eq_zero K).mpr
    intro v hv
    have H := hInv v v
    rw [hv,show ((0:X),(0:X))=0 from rfl,map_zero,zero_apply] at H
    exact inner_self_eq_zero.mp H.symm
  have hKsurj : Function.Surjective K :=
    (LinearMap.injective_iff_surjective (f := K.toLinearMap)).mp hKinj
  have hsym := (hB.isSymmSndFDerivAt (by norm_num)).eq
  have hKs (v w : X) : inner ℝ (K v) w=inner ℝ v (K w) := by
    have H := hsym (0,K v) (0,K w)
    rw [hInv,hInv] at H
    exact H.symm.trans (real_inner_comm _ _)
  have hKn (v : X) : 0≤ inner ℝ (K v) v := by
    have hmin : IsLocalMin (fun k : X => B (0,k)) p := by
      filter_upwards [] with k
      change splitNormalAction x t p (0,p)≤ splitNormalAction x t p (0,k)
      rw [splitNormalAction_contact hpG ht ht1]
      exact normalCost_le_splitNormalAction x p 0 k ht ht1
    have HC := hB.comp p (contDiffAt_const.prodMk contDiffAt_id)
    have H := localMin_hessian_nonneg HC hmin (K v)
    change 0 ≤ fderiv ℝ (fderiv ℝ (fun k : X => B (0,k))) p (K v) (K v) at H
    rw [second_derivative_target_slice hB,hInv] at H
    exact H
  refine ⟨K,⟨hKinj,hKsurj⟩,hKs,hKn,hInv,?_⟩
  intro v
  have H := stationary_graph_schur_hessian hBa
    (ha.of_le (m := 1) (by simp)) hstat v v
  rw [ha0,fixedSplitAction_source_hessian hpG ht ht1,hInv] at H
  have heq : (fun u => B (u,a u)) =ᶠ[𝓝 (0:X)] normalCost x p := he
  have heDD := (heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  rw [heDD] at H
  exact H

end SchurAction
end WeakMTWTransport

end

end

end

end OAI
