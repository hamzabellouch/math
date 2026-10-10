import Mathlib

namespace OAI

/-! Coalescing real and complex zeros through Rolle's theorem.

The affine specialization gives vanishing jets when distinct zeros converge to one point. -/

section

namespace CriticalHoneycomb.Analysis
open Set Filter Topology
lemma rolle_many (n : ℕ) (f : ℝ→ℝ) (a b : ℝ)
    (xs : Fin (n+1)→ℝ) (hxs : StrictMono xs)
    (hbound : ∀ i, xs i∈Icc a b) (hzero : ∀ i,f (xs i)=0)
    (hc : ∀ j : ℕ,j<n→ ContinuousOn (iteratedDeriv j f) (Icc a b)) :
    ∃ c∈Icc a b,iteratedDeriv n f c=0 := by
  induction n generalizing f with
  | zero => exact ⟨xs 0,hbound 0,by simpa using hzero 0⟩
  | succ n ih =>
    have hex : ∀ i : Fin (n+1),∃ c∈Ioo (xs i.castSucc) (xs i.succ),deriv f c=0 := by
      intro i
      apply exists_deriv_eq_zero (hxs (Fin.castSucc_lt_succ (i:=i)))
      · have hcf : ContinuousOn f (Icc a b) := by
          simpa only [iteratedDeriv_zero] using hc 0 (by omega)
        exact hcf.mono (Icc_subset_Icc (hbound i.castSucc).1 (hbound i.succ).2)
      · rw [hzero,hzero]
    choose cs hcs hcz using hex
    have hm : StrictMono cs := by
      intro i j hij
      have hij' : i.succ≤j.castSucc := by exact_mod_cast (show i.val+1≤j.val by omega)
      exact (hcs i).2.trans_le ((hxs.monotone hij').trans (hcs j).1.le)
    have hb : ∀ i,cs i∈Icc a b := fun i=>
      ⟨(hbound i.castSucc).1.trans (hcs i).1.le,(hcs i).2.le.trans (hbound i.succ).2⟩
    have hd : ∀ j : ℕ,j<n→ ContinuousOn (iteratedDeriv j (deriv f)) (Icc a b) := by
      intro j hj
      simpa only [←iteratedDeriv_succ'] using hc (j+1) (by omega)
    obtain ⟨c,hc,hz⟩:=ih (deriv f) cs hm hb hcz hd
    exact ⟨c,hc,by simpa only [iteratedDeriv_succ'] using hz⟩

lemma confluent_zero (n : ℕ) (f : ℝ→ℝ→ℝ) (r : ℕ→ℝ) (x : ℝ)
    (lo hi : ℕ→ℝ) (xs : (k : ℕ)→Fin (n+1)→ℝ)
    (hr : Tendsto r atTop (𝓝 0)) (hl : Tendsto lo atTop (𝓝 x))
    (hh : Tendsto hi atTop (𝓝 x))
    (hxs : ∀ k,StrictMono (xs k)) (hb : ∀ k i,xs k i∈Icc (lo k) (hi k))
    (hz : ∀ k i,f (r k) (xs k i)=0)
    (hc : ∀ k j,j<n→ ContinuousOn (iteratedDeriv j (f (r k))) (Icc (lo k) (hi k)))
    (hlim : ContinuousAt (fun p : ℝ×ℝ=>iteratedDeriv n (f p.1) p.2) (0,x)) :
    iteratedDeriv n (f 0) x=0 := by
  have hex : ∀ k,∃ c∈Icc (lo k) (hi k),iteratedDeriv n (f (r k)) c=0 :=
    fun k=>rolle_many n (f (r k)) (lo k) (hi k) (xs k) (hxs k) (hb k) (hz k) (hc k)
  choose cs hcs hcz using hex
  have hcs' : Tendsto cs atTop (𝓝 x) := tendsto_of_tendsto_of_tendsto_of_le_of_le hl hh (fun k=>(hcs k).1) (fun k=>(hcs k).2)
  have hp : Tendsto (fun k=>(r k,cs k)) atTop (𝓝 (0,x)) := hr.prodMk_nhds hcs'
  have hresult:=hlim.tendsto.comp hp
  have hzero : Tendsto (fun k=>iteratedDeriv n (f (r k)) (cs k)) atTop (𝓝 0) := by
    simpa only [hcz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0:ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hresult hzero
end CriticalHoneycomb.Analysis

end

section

open scoped ContDiff
namespace CriticalHoneycomb.Analysis
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma contDiffAt_partial_deriv (f : ℝ→ℝ→F) (r u : ℝ)
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (r,u)) :
    ContDiffAt ℝ ∞ (fun p : ℝ×ℝ=>deriv (f p.1) p.2) (r,u) := by
  let g : (ℝ×ℝ)→ℝ→F := fun p t=>f p.1 t
  have hproj : ContDiffAt ℝ ∞ (fun p : (ℝ×ℝ)×ℝ=>(p.1.1,p.2)) ((r,u),u) :=
    (contDiffAt_fst.fst).prodMk contDiffAt_snd
  have hg : ContDiffAt ℝ ∞ (Function.uncurry g) ((r,u),u) :=
    by simpa only [Function.comp_def,Function.uncurry_def,g] using
      (ContDiffAt.comp (f:=fun p : (ℝ×ℝ)×ℝ=>(p.1.1,p.2))
        (g:=Function.uncurry f) ((r,u),u) hf hproj)
  have hd : ContDiffAt ℝ ∞ (fun p : ℝ×ℝ=>fderiv ℝ (g p) p.2) (r,u) :=
    hg.fderiv (g:=fun p : ℝ×ℝ=>p.2) contDiffAt_snd (by simp)
  exact hd.clm_apply (contDiffAt_const (c:=(1:ℝ)))
lemma contDiffAt_partial_iteratedDeriv (n : ℕ) (f : ℝ→ℝ→F) (r u : ℝ)
    (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (r,u)) :
    ContDiffAt ℝ ∞ (fun p : ℝ×ℝ=>iteratedDeriv n (f p.1) p.2) (r,u) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero,Function.uncurry_def] using hf
  | succ n ih =>
    simpa only [iteratedDeriv_succ] using
      contDiffAt_partial_deriv (fun r=>iteratedDeriv n (f r)) r u ih
end CriticalHoneycomb.Analysis

end

section
open scoped ContDiff
namespace CriticalHoneycomb.Analysis
open Set Filter Topology
lemma confluent_zero_eventually {α : Type*} (l : Filter α) [l.NeBot]
    (n : ℕ) (f : ℝ→ℝ→ℝ) (r : α→ℝ) (x : ℝ)
    (lo hi : α→ℝ) (xs : α→Fin (n+1)→ℝ)
    (hr : Tendsto r l (𝓝 0)) (hl : Tendsto lo l (𝓝 x)) (hh : Tendsto hi l (𝓝 x))
    (hdata : ∀ᶠ k in l,StrictMono (xs k) ∧ (∀ i,xs k i∈Icc (lo k) (hi k)) ∧
      (∀ i,f (r k) (xs k i)=0) ∧
      (∀ j,j < n → ContinuousOn (iteratedDeriv j (f (r k))) (Icc (lo k) (hi k))))
    (hlim : ContinuousAt (fun p : ℝ×ℝ=>iteratedDeriv n (f p.1) p.2) (0,x)) :
    iteratedDeriv n (f 0) x=0 := by
  classical
  let P := fun k c=>c∈Icc (lo k) (hi k) ∧ iteratedDeriv n (f (r k)) c=0
  have hex : ∀ᶠ k in l,∃ c,P k c := by
    filter_upwards [hdata] with k hk
    exact rolle_many n (f (r k)) (lo k) (hi k) (xs k) hk.1 hk.2.1 hk.2.2.1 hk.2.2.2
  let cs : α→ℝ := fun k=>if h : ∃ c,P k c then Classical.choose h else x
  have hc : ∀ᶠ k in l,P k (cs k) := by
    filter_upwards [hex] with k hk
    simpa only [cs,dite_eq_left hk] using Classical.choose_spec hk
  have hcs : Tendsto cs l (𝓝 x) := tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hh
    (hc.mono (fun _ h=>h.1.1)) (hc.mono (fun _ h=>h.1.2))
  have hd:=hlim.tendsto.comp (hr.prodMk_nhds hcs)
  have hz : Tendsto (fun k=>iteratedDeriv n (f (r k)) (cs k)) l (𝓝 0) :=
    tendsto_const_nhds.congr' (hc.mono (fun _ h=>h.2.symm))
  exact tendsto_nhds_unique hd hz

lemma confluent_affine (n : ℕ) (f : ℝ→ℝ→ℝ) (x : ℝ)
    (a : Fin (n+1)→ℝ) (ha : StrictMono a) (C : ℝ) (hC : 0 < C)
    (hb : ∀ i,|a i|≤C) (δ : ℝ) (hδ : 0<δ)
    (hzero : ∀ r,0<r→ r < δ→∀ i,f r (x+r*a i)=0)
    (hsmooth : ∀ r u,|r| < δ→|u-x| < δ*C→
      ContDiffAt ℝ ∞ (Function.uncurry f) (r,u)) :
    iteratedDeriv n (f 0) x=0 := by
  have hr : Tendsto (id : ℝ→ℝ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hl : Tendsto (fun r : ℝ=>x-r*C) (𝓝[>] 0) (𝓝 x) := by
    simpa using (tendsto_const_nhds.sub (hr.mul_const C))
  have hh : Tendsto (fun r : ℝ=>x+r*C) (𝓝[>] 0) (𝓝 x) := by
    simpa using (tendsto_const_nhds.add (hr.mul_const C))
  apply confluent_zero_eventually (𝓝[>] 0) n f id x (fun r=>x-r*C) (fun r=>x+r*C)
    (fun r i=>x+r*a i) hr hl hh
  · have he : ∀ᶠ r : ℝ in 𝓝[>] 0,0<r ∧  r < δ := by
      exact (show ∀ᶠ r : ℝ in 𝓝[>] 0,0<r from self_mem_nhdsWithin).and ((eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds)
    filter_upwards [he] with r hr
    refine ⟨?_,?_,hzero r hr.1 hr.2,?_⟩
    · intro i j hij
      dsimp only
      linarith [mul_lt_mul_of_pos_left (ha hij) hr.1]
    · intro i
      have hai:=abs_le.mp (hb i)
      constructor <;> nlinarith
    · intro j hj u hu
      rcases hu with ⟨hu0,hu1⟩
      have hx : |u-x| < δ*C := by
        rw [abs_lt]
        constructor <;> nlinarith [mul_lt_mul_of_pos_right hr.2 hC]
      have hs:=hsmooth r u (by simpa only [abs_of_pos hr.1] using hr.2) hx
      have hd:=(contDiffAt_partial_iteratedDeriv j f r u hs).continuousAt
      exact (hd.comp (f:=fun t : ℝ=>(r,t)) (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  · apply (contDiffAt_partial_iteratedDeriv n f 0 x ?_).continuousAt
    exact hsmooth 0 x (by simpa using hδ) (by simpa using mul_pos hδ hC)
lemma iteratedDeriv_clm {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (A : F→L[ℝ] G)
    (n : ℕ) (f : ℝ→F) (x : ℝ) (hf : ContDiffAt ℝ ∞ f x) :
    iteratedDeriv n (fun u=>A (f u)) x=A (iteratedDeriv n f x) := by
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  change (iteratedFDeriv ℝ n (A ∘ f) x) (fun _=>1)=_
  rw [A.iteratedFDeriv_comp_left hf (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))]
  rfl

lemma confluent_affine_complex (n : ℕ) (f : ℝ→ℝ→ℂ) (x : ℝ)
    (a : Fin (n+1)→ℝ) (ha : StrictMono a) (C : ℝ) (hC : 0 < C)
    (hb : ∀ i,|a i|≤C) (δ : ℝ) (hδ : 0<δ)
    (hzero : ∀ r,0<r→ r < δ→∀ i,f r (x+r*a i)=0)
    (hsmooth : ∀ r u,|r| < δ→|u-x| < δ*C→
      ContDiffAt ℝ ∞ (Function.uncurry f) (r,u)) :
    iteratedDeriv n (f 0) x=0 := by
  have hf0 : ContDiffAt ℝ ∞ (f 0) x := by
    have h := hsmooth 0 x (by simpa using hδ) (by simpa using mul_pos hδ hC)
    exact h.comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hre := confluent_affine n (fun r u=>(f r u).re) x a ha C hC hb δ hδ
    (by intro r hr hd i;rw [hzero r hr hd i];rfl)
    (by intro r u hr hu;exact Complex.reCLM.contDiff.contDiffAt.comp (r,u) (hsmooth r u hr hu))
  have him := confluent_affine n (fun r u=>(f r u).im) x a ha C hC hb δ hδ
    (by intro r hr hd i;rw [hzero r hr hd i];rfl)
    (by intro r u hr hu;exact Complex.imCLM.contDiff.contDiffAt.comp (r,u) (hsmooth r u hr hu))
  change iteratedDeriv n (fun u=>Complex.reCLM (f 0 u)) x=0 at hre
  change iteratedDeriv n (fun u=>Complex.imCLM (f 0 u)) x=0 at him
  rw [iteratedDeriv_clm Complex.reCLM n (f 0) x hf0] at hre
  rw [iteratedDeriv_clm Complex.imCLM n (f 0) x hf0] at him
  exact Complex.ext hre him
end CriticalHoneycomb.Analysis

end


end OAI
