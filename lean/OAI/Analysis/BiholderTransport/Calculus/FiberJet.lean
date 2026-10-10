import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.JetDiffeomorphism

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma fiber_local_inverse
    (e:OpenPartialHomeomorph (E×F) (E×F)) (he:∀q,(e q).1=q.1)
    {b:E} {p:F} (hq:(b,p)∈e.source) :
    let f:=fun v:F=>(e (b,v)).2
    let g:=fun w:F=>(e.symm (b,w)).2
    (fun v=>g (f v)) =ᶠ[𝓝 p] id ∧ (fun w=>f (g w)) =ᶠ[𝓝 (f p)] id := by
  dsimp only
  have hf0:e (b,p)=(b,(e (b,p)).2) := Prod.ext (he _) rfl
  constructor
  · have H:∀ᶠ v in 𝓝 p,(b,v)∈e.source :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hq)
    filter_upwards [H] with v hv
    have Hinv:=e.left_inv hv
    have Hpair:e (b,v)=(b,(e (b,v)).2) := Prod.ext (he _) rfl
    calc
      _ = (e.symm (e (b,v))).2 := congrArg (fun q=>(e.symm q).2) Hpair.symm
      _ = v := congrArg Prod.snd Hinv
  · have ht:(b,(e (b,p)).2)∈e.target := hf0 ▸ e.map_source hq
    have H:∀ᶠ w in 𝓝 ((e (b,p)).2),(b,w)∈e.target :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (e.open_target.mem_nhds ht)
    filter_upwards [H] with w hw
    have Hinv:=e.right_inv hw
    have Hfirst:(e.symm (b,w)).1=b := by
      rw [←he (e.symm (b,w)),Hinv]
    have Hpair:e.symm (b,w)=(b,(e.symm (b,w)).2) := Prod.ext Hfirst rfl
    calc
      _ = (e (e.symm (b,w))).2 := congrArg (fun q=>(e q).2) Hpair.symm
      _ = w := congrArg Prod.snd Hinv

lemma fiber_jet_bound
    (e:OpenPartialHomeomorph (E×F) (E×F)) (he:∀q,(e q).1=q.1)
    {b:E} {p:F} (hq:(b,p)∈e.source)
    (hf:DifferentiableAt ℝ e (b,p)) (hg:DifferentiableAt ℝ e.symm (e (b,p)))
    {v:F → ℝ} {B:F →L[ℝ] F →L[ℝ] ℝ}
    (hjet:HasLowerSecondTaylor (fun d=>v ((e (b,p+d)).2)) 0 B)
    (hB:∀d,0 ≤ B d d) {C:ℝ} (hC:0 ≤ C)
    (hbound:∀ H:F →L[ℝ] F →L[ℝ] ℝ,(∀d,0 ≤ H d d) →
      HasLowerSecondTaylor (fun w=>v ((e (b,p)).2+w)) 0 H → ∀d,H d d ≤ C*‖d‖^2) :
    ∀d,B d d ≤ C*‖fderiv ℝ e (b,p)‖^2*‖d‖^2 := by
  let f:=fun v:F=>(e (b,v)).2
  let g:=fun w:F=>(e.symm (b,w)).2
  let T:=fderiv ℝ e (b,p)
  let A:F →L[ℝ] F := (ContinuousLinearMap.snd ℝ E F).comp
    (T.comp (ContinuousLinearMap.inr ℝ E F))
  have hsection:HasFDerivAt (fun v:F=>(b,v)) (ContinuousLinearMap.inr ℝ E F) p := by
    have hi:ContinuousLinearMap.inr ℝ E F=(0: F →L[ℝ] E).prod (ContinuousLinearMap.id ℝ F) := by
      ext d <;> rfl
    rw [hi]
    exact (hasFDerivAt_const b p).prodMk (hasFDerivAt_id p)
  have hAf:HasFDerivAt f A p := (hf.hasFDerivAt.comp p hsection).snd
  have hG:DifferentiableAt ℝ g (f p) := by
    have heq:(b,f p)=e (b,p) := by
      apply Prod.ext
      · exact (he (b,p)).symm
      · rfl
    have hg':DifferentiableAt ℝ e.symm (b,f p) := heq.symm ▸ hg
    exact (hg'.comp _ ((differentiableAt_const b).prodMk differentiableAt_id)).snd
  obtain ⟨hgf,hfg⟩:=fiber_local_inverse e he hq
  have H:=lower_jet_diffeomorphism_bound hAf hG.hasFDerivAt hgf hfg hjet hB hC hbound
  have hnorm:‖A‖ ≤ ‖T‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro d
    change ‖(T (0,d)).2‖ ≤ ‖T‖*‖d‖
    calc
      _ ≤ ‖T (0,d)‖ := norm_snd_le _
      _ ≤ ‖T‖*‖(0,d)‖ := T.le_opNorm _
      _ = ‖T‖*‖d‖ := by simp
  intro d
  exact (H d).trans (by gcongr)

lemma exists_uniform_fiber_jet_transfer
    (e:OpenPartialHomeomorph (E×F) (E×F)) (he:∀q,(e q).1=q.1)
    (hf:ContDiffOn ℝ ∞ e e.source) (hg:ContDiffOn ℝ ∞ e.symm e.target)
    {q:E×F} (hq:q∈e.source) :
    ∃ U:Set (E×F),U∈𝓝 q ∧ U⊆e.source ∧ ∃ K≥0,
      ∀z∈U,∀v:F → ℝ,∀B:F →L[ℝ] F →L[ℝ] ℝ,
      HasLowerSecondTaylor (fun d=>v ((e (z.1,z.2+d)).2)) 0 B →
      (∀d,0 ≤ B d d) → ∀C:ℝ,0 ≤ C →
      (∀ H:F →L[ℝ] F →L[ℝ] ℝ,(∀d,0 ≤ H d d) →
        HasLowerSecondTaylor (fun w=>v ((e z).2+w)) 0 H → ∀d,H d d ≤ C*‖d‖^2) →
      ∀d,B d d ≤ C*K*‖d‖^2 := by
  let R:=‖fderiv ℝ e q‖+1
  let U:=e.source ∩ {z|‖fderiv ℝ e z‖<R}
  have hR:0 < R := by dsimp [R]; positivity
  have hU:U∈𝓝 q := inter_mem (e.open_source.mem_nhds hq)
    (((hf.contDiffAt (e.open_source.mem_nhds hq)).continuousAt_fderiv (by simp)).norm.preimage_mem_nhds
      (gt_mem_nhds (show ‖fderiv ℝ e q‖<R by dsimp [R]; linarith)))
  refine ⟨U,hU,inter_subset_left,R^2,sq_nonneg _,?_⟩
  intro z hz v B hjet hB C hC HB d
  have HF: DifferentiableAt ℝ e z :=
    (hf.contDiffAt (e.open_source.mem_nhds hz.1)).differentiableAt (by simp)
  have HG: DifferentiableAt ℝ e.symm (e z) :=
    (hg.contDiffAt (e.open_target.mem_nhds (e.map_source hz.1))).differentiableAt (by simp)
  have H:=fiber_jet_bound e he hz.1 HF HG hjet hB hC HB d
  exact H.trans (by gcongr; exact hz.2.le)

end WeakMTWTransport

end

end OAI
