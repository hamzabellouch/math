import OAI.Analysis.LienardCycles.SharpFlow

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open scoped Topology NNReal
open Set Filter
open scoped Topology ContDiff NNReal

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuinticLienard.Sharpness
open GlobalODE PartialCalculus
noncomputable def turn : ℝ := 2*Real.pi
lemma turn_pos : 0<turn := by unfold turn;positivity
noncomputable def initial (p : ℝ × ℝ) : Space := (p.1,((0,p.2),0))
structure ReturnFamily where
  W : Space → Space
  K : ℝ≥0
  L : ℝ≥0
  lip : LipschitzWith K W
  bound : ∀ x,‖W x‖≤L
  σ : (ℝ × ℝ) → ℝ
noncomputable def ReturnFamily.path (R : ReturnFamily) (p : ℝ × ℝ) (t : ℝ) : Space :=
  flow R.W R.lip R.bound (initial p) t
noncomputable def ReturnFamily.Q (R : ReturnFamily) (p : ℝ × ℝ) : ℝ := (R.path p (R.σ p)).2.2
lemma ReturnFamily.continuous (R : ReturnFamily) : Continuous (fun pt : (ℝ × ℝ) × ℝ=>R.path pt.1 pt.2) :=
  (continuous_flow R.W R.lip R.bound).comp (show Continuous (fun pt : (ℝ × ℝ) × ℝ=>(initial pt.1,pt.2)) by unfold initial;fun_prop)
@[simp] lemma ReturnFamily.path_zero (R : ReturnFamily) (p : ℝ × ℝ) : R.path p 0=initial p := by simp [ReturnFamily.path]
lemma ReturnFamily.deriv (R : ReturnFamily) (p : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (R.path p) (R.W (R.path p t)) t := flow_deriv R.W R.lip R.bound _ _
lemma return_family {s : ℝ} (hs : 0<s) :
    ∃ R : ReturnFamily, ContDiffAt ℝ ω R.σ (0,s) ∧ R.σ (0,s)=turn ∧
      ContDiffAt ℝ ω R.Q (0,s) ∧
      (∀ᶠ b in 𝓝 s,R.Q (0,b)=-Real.pi*b^2*(4-5*b^2+b^4)) ∧
      ∀ᶠ p in 𝓝 ((0,s):ℝ × ℝ),0<R.σ p ∧ (R.path p (R.σ p)).2.1.1=0 ∧
        0<(R.path p (R.σ p)).2.1.2 ∧ 0<p.2 ∧ R.σ p<turn+1 ∧
        ∀ t ∈ Icc (-1) (turn+1),R.W (R.path p t)=V (R.path p t) := by
  obtain ⟨W,K,L,hK,hL,hm,ha,he⟩ := analytic_cutoff_along_compact_solution V isOpen_univ
    (field_contDiff.of_le (by simp)).contDiffOn (fun x _=>local_flow x)
    (a:=(-1:ℝ)) (b:=turn+1) (c:=0) (by norm_num) (by linarith [turn_pos])
    (circle_continuous s) (fun _ _=>mem_univ _) (fun t _=>circle_deriv s t)
  let g : (ℝ × ℝ) × ℝ → Space := fun pt=>flow W hK hL (initial pt.1) pt.2
  have hgc : Continuous g := (continuous_flow W hK hL).comp (show Continuous (fun pt : (ℝ × ℝ) × ℝ=>(initial pt.1,pt.2)) by unfold initial;fun_prop)
  have hg0 (p : ℝ × ℝ) : g (p,0)=initial p := by simp [g]
  have hmatch (t : ℝ) (ht : t ∈ Icc (-1) (turn+1)) : g ((0,s),t)=circle s t := by
    simpa [g,initial] using hm t ht
  have han (t : ℝ) (ht : t ∈ Icc (-1) (turn+1)) : ContDiffAt ℝ ω g ((0,s),t) := by
    have H := ha t ht
    simp only [circle_zero,sub_zero] at H
    exact H.comp (((0:ℝ),s),t) (show ContDiffAt ℝ ω (fun pt : (ℝ × ℝ) × ℝ=>(initial pt.1,pt.2)) ((0,s),t) by unfold initial;fun_prop)
  have heq (t : ℝ) (ht : t ∈ Icc (-1) (turn+1)) :
      ∀ᶠ pt in 𝓝 (((0,s):ℝ × ℝ),t),W (g pt)=V (g pt) := by
    have H := he t ht
    simp only [circle_zero,sub_zero] at H
    exact (show ContinuousAt (fun pt : (ℝ × ℝ) × ℝ=>(initial pt.1,pt.2)) ((0,s),t) by unfold initial;fun_prop).eventually H
  have hTm : turn ∈ Icc (-1) (turn+1) := ⟨by linarith [turn_pos],by linarith⟩
  have hd (p : ℝ × ℝ) (t : ℝ) : HasDerivAt (fun u=>g (p,u)) (W (g (p,t))) t := flow_deriv W hK hL (initial p) t
  let xp : Space →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.fst ℝ Plane ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Plane × ℝ)))
  have hxd : HasDerivAt (fun t=>(g ((0,s),t)).2.1.1) s turn := by
    have H := xp.hasFDerivAt.comp_hasDerivAt turn (hd (0,s) turn)
    rw [(heq turn hTm).self_of_nhds,hmatch turn hTm] at H
    simpa [xp,V,circle,turn] using! H
  have hxT : (g ((0,s),turn)).2.1.1=0 := by rw [hmatch turn hTm];simp [circle,turn]
  obtain ⟨σ,hσ,hσ0,hσeq,hσunique⟩ := transverse_hit (han turn hTm).snd.fst.fst hxd (ne_of_gt hs)
  have hσx : ∀ᶠ p in 𝓝 ((0,s):ℝ × ℝ),(g (p,σ p)).2.1.1=0 := by simpa only [hxT] using hσeq
  have hfaith : ∀ᶠ p in 𝓝 ((0,s):ℝ × ℝ),∀ t ∈ Icc (-1) (turn+1),W (g (p,t))=V (g (p,t)) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    exact heq
  have hpos : ∀ᶠ p in 𝓝 ((0,s):ℝ × ℝ),0<σ p := hσ.continuousAt.eventually (eventually_gt_nhds (by rw [hσ0];exact turn_pos))
  have hbound : ∀ᶠ p in 𝓝 ((0,s):ℝ × ℝ),σ p<turn+1 := hσ.continuousAt.eventually (eventually_lt_nhds (by rw [hσ0];linarith))
  have hpc : ContinuousAt (fun p : ℝ × ℝ=>(p,σ p)) (0,s) := continuousAt_id.prodMk hσ.continuousAt
  have hhigh : ∀ᶠ p in 𝓝 ((0,s):ℝ × ℝ),0<(g (p,σ p)).2.1.2 := by
    apply (hgc.snd.fst.snd.continuousAt.comp hpc).eventually
    exact eventually_gt_nhds (by dsimp only [Function.comp_def];rw [hσ0,hmatch turn hTm];simpa [circle,turn] using hs)
  have hstart : ∀ᶠ p in 𝓝 ((0,s):ℝ × ℝ),0<p.2 := continuous_snd.continuousAt.eventually (eventually_gt_nhds hs)
  have hQ : ContDiffAt ℝ ω (fun p : ℝ × ℝ=>(g (p,σ p)).2.2) (0,s) := by
    have H : ContDiffAt ℝ ω g ((0,s),σ (0,s)) := by rw [hσ0];exact han turn hTm
    exact (H.comp (0,s) (contDiffAt_id.prodMk hσ)).snd.snd
  have hbb : ContinuousAt (fun b : ℝ=>((0,b):ℝ × ℝ)) s := continuousAt_const.prodMk continuousAt_id
  have hbf := hbb.eventually hfaith
  have hbuniq : ∀ᶠ b in 𝓝 s,(g ((0,b),turn)).2.1.1=0 ↔ σ (0,b)=turn := by
    have H := (hbb.prodMk continuousAt_const).eventually hσunique
    simpa only [hxT] using H
  have href : ∀ᶠ b in 𝓝 s,g ((0,b),turn)=circle b turn := by
    filter_upwards [hbf] with b hb
    have H := unique_on_open_interval V isOpen_univ (field_contDiff.of_le (by simp)).contDiffOn
      (a:=(-1:ℝ)) (b:=turn+1) (c:=0) (by constructor <;> linarith [turn_pos])
      (fun t ht=>⟨by rw [←hb t (Ioo_subset_Icc_self ht)];exact hd (0,b) t,mem_univ _⟩)
      (fun t _=>⟨circle_deriv b t,mem_univ _⟩) (by simp [hg0,initial])
    exact H ⟨by linarith [turn_pos],by linarith⟩
  let R : ReturnFamily := ⟨W,K,L,hK,hL,σ⟩
  refine ⟨R,hσ,hσ0,hQ,?_,?_⟩
  · filter_upwards [href,hbuniq] with b hb hu
    have hx : (g ((0,b),turn)).2.1.1=0 := by rw [hb];simp [circle,turn]
    change (g ((0,b),σ (0,b))).2.2=-Real.pi*b^2*(4-5*b^2+b^4)
    rw [hu.mp hx,hb]
    exact q_turn b
  · filter_upwards [hpos,hσx,hhigh,hstart,hbound,hfaith] with p hp hx hy hb ht hf
    exact ⟨hp,hx,hy,hb,ht,hf⟩
end QuinticLienard.Sharpness

end OAI
