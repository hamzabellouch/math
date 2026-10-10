import OAI.Analysis.LienardCycles.BoundaryFlow

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open Set Filter Metric
open scoped Topology ContDiff

open Set Filter Metric
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open PartialCalculus

theorem boundary_germ {V : (ℝ×ℝ) → ℝ×ℝ} {U : Set (ℝ×ℝ)}
    (hU : IsOpen U) (hV : ContDiffOn ℝ 1 V U)
    {y : ℝ×ℝ → ℝ} {t₀ A T : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 t₀) (hT : 0<T)
    (ha : ∀ x ∈ Ioo 0 T, ContDiffAt ℝ ω y (t₀,x))
    (he : ∀ t ∈ J, ∀ x ∈ Ioo 0 T,
      HasDerivAt (fun s=>(s,y (t,s))) (V (x,y (t,x))) x ∧ (x,y (t,x)) ∈ U)
    (hlim : Tendsto (fun x=>y (t₀,x)) (𝓝[>] 0) (𝓝 A))
    (hf : ∃ f : ((ℝ×ℝ)×ℝ) → ℝ×ℝ, ContDiffAt ℝ ω f ((0,A),0) ∧
      ∀ᶠ q in 𝓝 ((0,A),(0:ℝ)), f (q.1,0)=q.1 ∧
        HasDerivAt (fun s=>f (q.1,s)) (V (f q)) q.2)
    (hAU : (0,A) ∈ U) :
    ∃ G : ℝ×ℝ → ℝ, ContDiffAt ℝ ω G (t₀,0) ∧ G (t₀,0)=A ∧
      (∀ᶠ q in 𝓝 (t₀,(0:ℝ)), 0<q.2 → G q=y q) ∧
      ∃ δ ∈ Ioo 0 T, ∃ k : ℝ, 0<k ∧ first G (t₀,0)=k*first y (t₀,δ) := by
  obtain ⟨f,hfa,hfe⟩ := hf
  let e : (ℝ×ℝ)×ℝ := ((0,1),0)
  let F : ((ℝ×ℝ)×ℝ) → ℝ := fun q=>(f q).2
  have hFa : ContDiffAt ℝ ω F ((0,A),0) := hfa.snd
  have hD : direction e F ((0,A),0)=1 := by
    have hpath : HasDerivAt (fun s=>F ((0,s),0)) (direction e F ((0,A),0)) A := by
      simpa only [direction,e,Function.comp_def,id_eq] using hFa.differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt A
        (((hasDerivAt_const A (0:ℝ)).prodMk (hasDerivAt_id A)).prodMk (hasDerivAt_const A (0:ℝ)))
    have heq : (fun s=>F ((0,s),0)) =ᶠ[𝓝 A] (fun s=>s) := by
      filter_upwards [((continuousAt_const.prodMk continuousAt_id).prodMk continuousAt_const).eventually hfe] with s hs
      exact congrArg Prod.snd hs.1
    exact (hpath.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id A)
  have hpos : ∀ᶠ q in 𝓝 ((0,A),(0:ℝ)), 0<direction e F q := by
    exact (direction_contDiffAt hFa e).continuousAt.eventually (eventually_gt_nhds (by simpa only [hD] using (zero_lt_one : (0:ℝ)<1)))
  have hfu : ∀ᶠ q in 𝓝 ((0,A),(0:ℝ)), f q ∈ U := by
    have hval := hfe.self_of_nhds.1
    exact hfa.continuousAt.eventually (hU.mem_nhds (by simpa only [hval] using hAU))
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp
    ((hfa.eventually (by simp)).and (hfe.and (hpos.and hfu)))
  have hzl : Tendsto (fun x : ℝ=>(x,y (t₀,x))) (𝓝[>] 0) (𝓝 (0,A)) :=
    ((continuousAt_id : ContinuousAt (fun x : ℝ=>x) 0).tendsto.mono_left inf_le_left).prodMk_nhds hlim
  have hzsmall : ∀ᶠ x in 𝓝[>] (0:ℝ), dist (x,y (t₀,x)) (0,A)<ρ/2 :=
    hzl (Metric.ball_mem_nhds _ (by linarith))
  have hex : ∀ᶠ x in 𝓝[>] (0:ℝ), 0<x ∧ x<T ∧ x<ρ/4 ∧ dist (x,y (t₀,x)) (0,A)<ρ/2 := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hT).filter_mono inf_le_left,
      (eventually_lt_nhds (show (0:ℝ)<ρ/4 by linarith)).filter_mono inf_le_left,hzsmall] with x hx hxT hxρ hxz
    exact ⟨hx,hxT,hxρ,hxz⟩
  obtain ⟨δ,hδ,hδT,hδρ,hδz⟩ := hex.exists
  have hzcont : ContinuousAt (fun t : ℝ=>(δ,y (t,δ))) t₀ := continuousAt_const.prodMk
    ((ha δ ⟨hδ,hδT⟩).continuousAt.comp (f:=fun t : ℝ=>(t,δ)) (continuousAt_id.prodMk continuousAt_const))

  have hzN' : ∀ᶠ t in 𝓝 t₀, dist (δ,y (t,δ)) (0,A)<ρ/2 :=
    (hzcont.dist continuousAt_const).eventually (eventually_lt_nhds hδz)
  let G : ℝ×ℝ → ℝ := fun q=>F ((δ,y (q.1,δ)),q.2-δ)
  have hnear (t x : ℝ) (ht : dist (δ,y (t,δ)) (0,A)<ρ/2) (hx : |x|<2*δ) :
      ((δ,y (t,δ)),x-δ) ∈ ball ((0,A),0) ρ := by
    rw [mem_ball,Prod.dist_eq,max_lt_iff,Real.dist_eq,sub_zero]
    constructor
    · linarith
    · have hb := abs_le.mp (le_of_lt hx)
      rw [abs_lt]
      constructor <;> linarith
  have hzero := hball (hnear t₀ 0 hδz (by simpa only [abs_zero] using mul_pos (by norm_num : (0:ℝ)<2) hδ))
  have hinner : ContDiffAt ℝ ω (fun q : ℝ×ℝ=>((δ,y (q.1,δ)),q.2-δ)) (t₀,0) :=
    (contDiffAt_const.prodMk ((ha δ ⟨hδ,hδT⟩).comp (t₀,(0:ℝ))
      (contDiffAt_fst.prodMk contDiffAt_const))).prodMk (contDiffAt_snd.sub contDiffAt_const)
  have hGF : ContDiffAt ℝ ω F ((δ,y (t₀,δ)),0-δ) := hzero.1.snd
  have hGa : ContDiffAt ℝ ω G (t₀,0) := hGF.comp (f:=fun q : ℝ×ℝ=>((δ,y (q.1,δ)),q.2-δ)) (t₀,0) hinner
  have hag : ∀ᶠ q in 𝓝 (t₀,(0:ℝ)), 0<q.2 → G q=y q := by
    have hpN : ∀ᶠ t in 𝓝 t₀, t ∈ J ∧ dist (δ,y (t,δ)) (0,A)<ρ/2  := (show ∀ᶠ t in 𝓝 t₀, t ∈ J from hJ).and hzN'
    have hdN : ∀ᶠ x in 𝓝 (0:ℝ), |x|<δ := (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using hδ)
    filter_upwards [continuousAt_fst.eventually hpN,continuousAt_snd.eventually hdN] with q hq hqx hx
    let γ : ℝ → ℝ×ℝ := fun s=>(s,y (q.1,s))
    let ψ : ℝ → ℝ×ℝ := fun s=>f ((δ,y (q.1,δ)),s-δ)
    have hdomain : ∀ s ∈ Ioo 0 (min T (2*δ)), |s|<2*δ := by
      intro s hs
      simpa only [abs_of_pos hs.1] using hs.2.trans_le (min_le_right _ _)
    have hc : δ ∈ Ioo 0 (min T (2*δ)) := ⟨hδ,lt_min hδT (by linarith)⟩
    have heq := GlobalODE.unique_on_open_interval V hU hV hc
      (fun s hs=>he q.1 hq.1 s ⟨hs.1,hs.2.trans_le (min_le_left _ _)⟩)
      (fun s hs=>by
        have hfq := hball (hnear q.1 s hq.2 (hdomain s hs))
        refine ⟨?_,hfq.2.2.2⟩
        have hd : HasDerivAt (fun v=>f ((δ,y (q.1,δ)),v)) (V (f ((δ,y (q.1,δ)),s-δ))) (s-δ) := hfq.2.1.2
        simpa only [one_smul,Function.comp_def,id_eq] using hd.scomp (h:=fun v : ℝ=>v-δ) s ((hasDerivAt_id s).sub_const δ))
      (show γ δ=ψ δ by
        dsimp only [γ,ψ]
        rw [sub_self]
        exact (hball (hnear q.1 δ hq.2 (by rw [abs_of_pos hδ]; linarith))).2.1.1.symm)
    have hxx : q.2 ∈ Ioo 0 (min T (2*δ)) := ⟨hx,lt_min
      ((lt_of_le_of_lt (le_abs_self _) hqx).trans hδT) (by linarith [le_abs_self q.2])⟩
    exact (congrArg Prod.snd (heq hxx)).symm
  have hGlim : Tendsto (fun x=>G (t₀,x)) (𝓝[>] 0) (𝓝 (G (t₀,0))) :=
    ((hGa.continuousAt.comp (continuousAt_const.prodMk continuousAt_id))).tendsto.mono_left inf_le_left
  have heq0 : (fun x=>G (t₀,x)) =ᶠ[𝓝[>] 0] (fun x=>y (t₀,x)) := by
    filter_upwards [((continuousAt_const.prodMk continuousAt_id).eventually hag).filter_mono inf_le_left,
      self_mem_nhdsWithin] with x hx hx0
    exact hx hx0
  have hzero' := hzero
  simp only [zero_sub] at hzero'
  refine ⟨G,hGa,tendsto_nhds_unique hGlim (hlim.congr' heq0.symm),hag,δ,⟨hδ,hδT⟩,
    direction e F ((δ,y (t₀,δ)),-δ),hzero'.2.2.1,?_⟩
  have hdy := first_hasDerivAt ((ha δ ⟨hδ,hδT⟩).differentiableAt (by simp))
  have hdG := hzero'.1.snd.differentiableAt (by simp) |>.hasFDerivAt.comp_hasDerivAt t₀
    (((hasDerivAt_const t₀ δ).prodMk hdy).prodMk (hasDerivAt_const t₀ (-δ)))
  have heqD : ((0,first y (t₀,δ)),0)=first y (t₀,δ) • e := by ext <;> simp [e]
  have hdval : first G (t₀,0)=fderiv ℝ F ((δ,y (t₀,δ)),-δ) ((0,first y (t₀,δ)),0) := by
    exact (first_hasDerivAt (hGa.differentiableAt (by simp))).unique (by simpa only [G,F,Function.comp_def,zero_sub] using hdG)
  rw [hdval,heqD,map_smul]
  simp only [smul_eq_mul, direction]
  ring
end QuinticLienard.AxisFlow

end OAI
