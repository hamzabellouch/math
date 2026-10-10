import OAI.Analysis.LienardCycles.StableExcursion

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuinticLienard
open ScaledProfile GlobalODE PartialCalculus
structure ReturnFlow where
  W : Plane → Plane
  K : ℝ≥0
  L : ℝ≥0
  lip : LipschitzWith K W
  bound : ∀ x,‖W x‖≤L
  τ : ℝ → ℝ
  σ : ℝ → ℝ
noncomputable def ReturnFlow.path (R : ReturnFlow) (s t : ℝ) : Plane := flow R.W R.lip R.bound (0,s) t
lemma ReturnFlow.continuous (R : ReturnFlow) : Continuous (fun p : ℝ × ℝ=>R.path p.1 p.2) :=
  (continuous_flow R.W R.lip R.bound).comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
@[simp] lemma ReturnFlow.path_zero (R : ReturnFlow) (s : ℝ) : R.path s 0=(0,s) := by simp [ReturnFlow.path]
lemma IsSolution.return_neighborhood {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) {z : ℝ → Plane} (hz : IsSolution F z)
    {S T : ℝ} (hS : 0<S) (hST : S<T) (hp : Function.Periodic z T)
    (hr : IsRightExcursion z 0 S) (hl : IsRightExcursion (QuinticLienard.reverseX z) (-T) (-S)) :
    ∃ R : ReturnFlow,
      ContDiffAt ℝ ω R.τ (z 0).2 ∧ ContDiffAt ℝ ω R.σ (z 0).2 ∧ R.τ (z 0).2=S ∧ R.σ (z 0).2=T ∧
      (∀ t ∈ Icc (-1) (T+1),R.path (z 0).2 t=z t) ∧
      (∀ᶠ s in 𝓝 (z 0).2,0<R.τ s ∧ R.τ s<R.σ s ∧
        IsRightExcursion (R.path s) 0 (R.τ s) ∧
        IsRightExcursion (QuinticLienard.reverseX (R.path s)) (-R.σ s) (-R.τ s) ∧
        (R.path s (R.τ s)).2<F.eval 0 ∧ F.eval 0<s ∧ F.eval 0<(R.path s (R.σ s)).2 ∧
        ∀ t ∈ Icc 0 (R.σ s),R.W (R.path s t)=vectorField F (R.path s t)) ∧
      ∀ U : Set Plane,IsOpen U → range z ⊆ U →
        ∀ᶠ s in 𝓝 (z 0).2,∀ t ∈ Icc 0 (R.σ s),R.path s t ∈ U := by
  have hT := hS.trans hST
  have hnon : ∃ u v,z u≠z v := by
    refine ⟨0,S/2,?_⟩
    intro he
    have hpos := hr.positive (S/2) ⟨by linarith,by linarith⟩
    rw [←he,hr.left] at hpos
    exact lt_irrefl _ hpos
  have hsign := hr.endpoint_signs hz hnon
  have hzT : z T=z 0 := by simpa using hp 0
  obtain ⟨W,K,L,hK,hL,hm,ha,he⟩ := hz.cutoff hF hT
  let f : ℝ × ℝ → Plane := fun q=>flow W hK hL (0,q.1) q.2
  have hfc : Continuous f := (continuous_flow W hK hL).comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
  have hinit : ((0,(z 0).2):Plane)=z 0 := Prod.ext hr.left.symm rfl
  have hmatch (t : ℝ) (ht : t ∈ Icc (-1) (T+1)) : f ((z 0).2,t)=z t := by simpa [f,hinit] using hm t ht
  have han (t : ℝ) (ht : t ∈ Icc (-1) (T+1)) : ContDiffAt ℝ ω f ((z 0).2,t) := by
    have hg : ContDiffAt ℝ ω (fun q : ℝ × ℝ => (((0 : ℝ),q.1),q.2)) ((z 0).2,t) :=
      (contDiffAt_const.prodMk contDiffAt_fst).prodMk contDiffAt_snd
    have hh : ContDiffAt ℝ ω (fun q : Plane × ℝ=>flow W hK hL q.1 q.2) ((0,(z 0).2),t) := by
      simpa only [hinit] using ha t ht
    exact hh.comp ((z 0).2,t) hg
  have hd (s t : ℝ) : HasDerivAt (fun v=>f (s,v)) (W (f (s,t))) t := flow_deriv W hK hL (0,s) t
  have hxd (s t : ℝ) : HasDerivAt (fun v=>(f (s,v)).1) (W (f (s,t))).1 t := by
    simpa using! (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hd s t)
  have heq (t : ℝ) (ht : t ∈ Icc (-1) (T+1)) : ∀ᶠ q in 𝓝 ((z 0).2,t),W (f q)=vectorField F (f q) := by
    have hh : ContinuousAt (fun q : ℝ × ℝ=>(((0:ℝ),q.1),q.2)) ((z 0).2,t) := by fun_prop
    have hhe := he t ht
    rw [←hinit] at hhe
    exact hh.eventually hhe
  have hSm : S ∈ Icc (-1) (T+1) := ⟨by linarith,by linarith⟩
  have hTm : T ∈ Icc (-1) (T+1) := ⟨by linarith,by linarith⟩
  have h0m : (0:ℝ) ∈ Icc (-1) (T+1) := ⟨by norm_num,by linarith⟩
  have hxS : (f ((z 0).2,S)).1=0 := by rw [hmatch S hSm,hr.right]
  have hxT : (f ((z 0).2,T)).1=0 := by rw [hmatch T hTm,hzT,hr.left]
  have hvS : (W (f ((z 0).2,S))).1=(z S).2-F.eval 0 := by
    rw [(heq S hSm).self_of_nhds,hmatch S hSm];simp [vectorField,hr.right]
  have hvT : (W (f ((z 0).2,T))).1=(z 0).2-F.eval 0 := by
    rw [(heq T hTm).self_of_nhds,hmatch T hTm,hzT];simp [vectorField,hr.left]
  obtain ⟨τ,hτ,hτ0,hτeq,_⟩ := transverse_hit (han S hSm).fst (hxd (z 0).2 S)
    (by rw [hvS];exact sub_ne_zero.mpr hsign.1.ne)
  obtain ⟨σ,hσ,hσ0,hσeq,_⟩ := transverse_hit (han T hTm).fst (hxd (z 0).2 T)
    (by rw [hvT];exact sub_ne_zero.mpr hsign.2.ne')
  have hτx : ∀ᶠ s in 𝓝 (z 0).2,(f (s,τ s)).1=0 := by simpa only [hxS] using hτeq
  have hσx : ∀ᶠ s in 𝓝 (z 0).2,(f (s,σ s)).1=0 := by simpa only [hxT] using hσeq
  have hv0 : (W (f ((z 0).2,0))).1=(z 0).2-F.eval 0 := by
    rw [(heq 0 h0m).self_of_nhds,hmatch 0 h0m];simp [vectorField,hr.left]
  have rightStable := stable_positive_between (α:=fun _ : ℝ=>(0:ℝ)) hxd hfc.fst (hK.continuous.comp hfc |>.fst)
    continuousAt_const hτ.continuousAt
    (Filter.Eventually.of_forall fun s=>by simp [f]) hτx
    (by simpa only [hτ0] using hS)
    (fun t ht=>by
      rw [hτ0] at ht
      rw [hmatch t ⟨by linarith [ht.1],by linarith [ht.2]⟩]
      exact hr.positive t ht)
    (by dsimp only [Function.comp_def,Pi.neg_apply];rw [hv0];exact sub_pos.mpr hsign.2)
    (by dsimp only [Function.comp_def,Pi.neg_apply];rw [hτ0,hvS];exact sub_neg.mpr hsign.1)
  have leftStable := stable_positive_between (fun s t=>(hxd s t).neg) hfc.fst.neg (hK.continuous.comp hfc |>.fst.neg)
    hτ.continuousAt hσ.continuousAt (hτx.mono fun _ h=>by simp [h]) (hσx.mono fun _ h=>by simp [h])
    (by simpa only [hτ0,hσ0] using hST)
    (fun t ht=>by
      rw [hτ0,hσ0] at ht
      dsimp only [Pi.neg_apply]
      rw [hmatch t ⟨by linarith [ht.1],by linarith [ht.2]⟩]
      simpa [QuinticLienard.reverseX] using hl.positive (-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩)
    (by dsimp only [Function.comp_def,Pi.neg_apply];rw [hτ0,hvS];linarith [hsign.1])
    (by dsimp only [Function.comp_def,Pi.neg_apply];rw [hσ0,hvT];linarith [hsign.2])
  have hfaith : ∀ᶠ s in 𝓝 (z 0).2,∀ t ∈ Icc 0 (T+1),W (f (s,t))=vectorField F (f (s,t)) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    exact fun t ht=>heq t ⟨by linarith [ht.1],ht.2⟩
  have hσbound : ∀ᶠ s in 𝓝 (z 0).2,σ s<T+1 := hσ.continuousAt.eventually (eventually_lt_nhds (show σ (z 0).2<T+1 by rw [hσ0];linarith))
  have hlow : ∀ᶠ s in 𝓝 (z 0).2,(f (s,τ s)).2<F.eval 0 := by
    have hc := hfc.snd.continuousAt.comp (continuousAt_id.prodMk hτ.continuousAt)
    exact hc.eventually (eventually_lt_nhds (by simpa only [Function.comp_def,id_eq,hτ0,hmatch S hSm] using hsign.1))
  have hhigh : ∀ᶠ s in 𝓝 (z 0).2,F.eval 0<(f (s,σ s)).2 := by
    have hc := hfc.snd.continuousAt.comp (continuousAt_id.prodMk hσ.continuousAt)
    exact hc.eventually (eventually_gt_nhds (by simpa only [Function.comp_def,id_eq,hσ0,hmatch T hTm,hzT] using hsign.2))
  let R : ReturnFlow := ⟨W,K,L,hK,hL,τ,σ⟩
  refine ⟨R,hτ,hσ,hτ0,hσ0,hmatch,?_,?_⟩
  · filter_upwards [rightStable,leftStable,hτx,hσx,hlow,hhigh,hfaith,hσbound,eventually_gt_nhds hsign.2] with s hrs hls hτs hσs hlo hhi hfa hbo hstart
    refine ⟨hrs.1,hls.1,⟨hrs.1,by simp [R,ReturnFlow.path],hτs,hrs.2⟩,?_,hlo,hstart,hhi,?_⟩
    · refine ⟨by dsimp [R];linarith [hls.1],?_,?_,?_⟩
      · simpa [QuinticLienard.reverseX,R,ReturnFlow.path,f] using congrArg Neg.neg hσs
      · simpa [QuinticLienard.reverseX,R,ReturnFlow.path,f] using congrArg Neg.neg hτs
      · intro t ht
        exact hls.2 (-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
    · intro t ht
      exact hfa t ⟨ht.1,ht.2.trans hbo.le⟩
  · intro U hU hzU
    have hu : ∀ᶠ s in 𝓝 (z 0).2,∀ t ∈ Icc 0 (T+1),f (s,t) ∈ U := by
      apply isCompact_Icc.eventually_forall_of_forall_eventually
      intro t ht
      apply hfc.continuousAt.eventually
      rw [hmatch t ⟨by linarith [ht.1],ht.2⟩]
      exact hU.mem_nhds (hzU (mem_range_self t))
    filter_upwards [hu,hσbound] with s hs hb t ht
    exact hs t ⟨ht.1,ht.2.trans hb.le⟩
end QuinticLienard

end OAI
