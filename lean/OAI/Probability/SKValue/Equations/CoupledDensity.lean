import Mathlib
import OAI.Probability.SKValue.Evolution.JetParity

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology
namespace SKValue
structure ForwardShape (c:ℝ) (A:ℝ → ℝ) (D:ForwardDensityData) : Prop where
  slope : ∀ x,1/D.variance≤D.jet 1 x
  concave : ∀ x,0≤x → D.jet 2 x≤0
  coupled : ∀ x,0≤x → 0≤ spatialJet c A 0 x*D.jet 1 x-D.jet 0 x*spatialJet c A 1 x

lemma BackwardShape.gaussian_forwardShape {A:ℝ → ℝ} {c:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape c A) {a:ℝ} (ha:0<a) :
    ForwardShape c A (ForwardDensityData.gaussian a ha) := by
  refine ⟨?_,?_,?_⟩
  · intro x;rw [ForwardDensityData.gaussian_jet];simp [ForwardDensityData.gaussian]
  · intro x hx;rw [ForwardDensityData.gaussian_jet];norm_num
  · intro x hx
    simp only [ForwardDensityData.gaussian_jet,ite_true,Nat.one_ne_zero,ite_false]
    have h0:spatialJet c A 0 0=0 := by simp [spatialJet,deriv_even_zero hB.even]
    let p:=fun y ↦ spatialJet c A 0 y-y*spatialJet c A 1 y
    have hd (y:ℝ):HasDerivAt p (-y*spatialJet c A 2 y) y := by
      convert! (hA.spatialJet_space c 0 y).sub ((hasDerivAt_id y).mul (hA.spatialJet_space c 1 y)) using 1; dsimp [p]; ring
    have hm:MonotoneOn p (Ici 0) := monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y hy ↦ (hd y).continuousAt.continuousWithinAt)
      (fun y hy ↦ (hd y).differentiableAt.differentiableWithinAt)
      (fun y hy ↦ by
        rw [(hd y).deriv]
        exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (interior_subset hy)) (hB.w y (interior_subset hy)))
    have hh:=hm (show (0:ℝ)∈Ici 0 from by simp) hx hx
    have hp:p 0=0 := by simp [p,h0]
    rw [hp] at hh
    have hh':0≤p x/a := div_nonneg hh ha.le
    convert! hh' using 1; dsimp [p]; ring

lemma ForwardShape.evolve_coupled_interior {A:ℝ → ℝ} {c h t:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape c A) (hc:0<c) (ht:0≤t) (hth:t<h) {D:ForwardDensityData}
    (hF:ForwardShape c (coleHopf c h A) D) (x:ℝ) (hx:0≤x) :
    0≤ scaledHeatJet c A 0 (h-t) x*forwardJet D.variance D.size D.potential 1 t x-
      forwardJet D.variance D.size D.potential 0 t x*scaledHeatJet c A 1 (h-t) x := by
  let B:=hA.backwardBurgers hB.even hB.convex hc
  let F:=D.smooth.forwardBurgers D.even D.variance_pos D.size_pos t
  have hinit:∀ y,0≤y → 0≤B.ratioJ F h 0 y := by
    intro y hy
    simpa only [BackwardBurgers.ratioJ,B,F,SmoothTerminal.forwardBurgers,
      SmoothTerminal.backwardBurgers,scaledHeatJet,sub_zero,←D.jet_initial,spatialJet]
      using hF.coupled y hy
  have hslope:∀ x,1/D.variance≤F.jet 1 0 x := by
    simpa only [F,SmoothTerminal.forwardBurgers,←D.jet_initial] using hF.slope
  have hsconc:∀ x,0≤x → F.jet 2 0 x≤0 := by
    simpa only [F,SmoothTerminal.forwardBurgers,←D.jet_initial] using hF.concave
  have hw:∀ u∈Icc (0:ℝ) t,∀ y,0≤y → B.jet 2 (h-u) y≤0 := by
    intro u hu y hy
    exact (hB.evolve hA hc (by linarith [hu.2])).w y hy
  have hn:∀ u∈Icc (0:ℝ) t,∀ y,0≤y → 0≤B.n (h-u) y := by
    intro u hu y hy
    exact (hB.evolve hA hc (by linarith [hu.2])).n y hy
  exact B.ratioJ_nonneg F D.variance_pos ht hth hinit hslope hsconc hw hn t ⟨ht,le_rfl⟩ x hx

lemma coupled_pair_continuous {A:ℝ → ℝ} {c h:ℝ} (hA:SmoothTerminal A)
    (hc:0≤c) (D:ForwardDensityData) (x:ℝ) :
    Continuous (fun t:ℝ ↦ scaledHeatJet c A 0 (h-t) x*forwardJet D.variance D.size D.potential 1 t x-
      forwardJet D.variance D.size D.potential 0 t x*scaledHeatJet c A 1 (h-t) x) := by
  have hmap:Continuous (fun t:ℝ ↦ (h-t,x)) := (continuous_const.sub continuous_id).prodMk continuous_const
  have hmap':Continuous (fun t:ℝ ↦ (t,x)) := continuous_id.prodMk continuous_const
  have hb (n:ℕ):Continuous (fun t:ℝ ↦ scaledHeatJet c A n (h-t) x) := by
    have hf:=scaledHeatJet_continuous hA hc n
    have hh:=Continuous.comp hf hmap
    convert! hh using 1
  have hf (n:ℕ):Continuous (fun t:ℝ ↦ forwardJet D.variance D.size D.potential n t x) := by
    have hf:=forwardJet_continuous D.smooth D.variance_pos D.size_pos.le n
    have hh:=Continuous.comp hf hmap'
    convert! hh using 1
  exact ((hb 0).mul (hf 1)).sub ((hf 0).mul (hb 1))

lemma ForwardShape.evolve {A:ℝ → ℝ} {c h:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape c A) (hc:0<c) (hh:0≤h) {D:ForwardDensityData}
    (hF:ForwardShape c (coleHopf c h A) D) :
    ForwardShape c A (D.evolve h hh) := by
  obtain ⟨hsl,hsc⟩:=D.evolve_slope_concavity hF.slope hF.concave hh
  refine ⟨hsl,hsc,?_⟩
  intro x hx
  let R:=fun t ↦ scaledHeatJet c A 0 (h-t) x*forwardJet D.variance D.size D.potential 1 t x-
    forwardJet D.variance D.size D.potential 0 t x*scaledHeatJet c A 1 (h-t) x
  have hhR:0≤R h := by
    by_cases hh0:h=0
    · subst h
      simpa only [R,scaledHeatJet,sub_zero,←D.jet_initial,spatialJet] using hF.coupled x hx
    · have hhp:0<h := lt_of_le_of_ne hh (Ne.symm hh0)
      have hcR:Continuous R := coupled_pair_continuous hA hc.le D x
      have htend:Tendsto R (𝓝[<] h) (𝓝 (R h)) := hcR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      apply ge_of_tendsto htend
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hhp)] with t ht ht0
      exact hF.evolve_coupled_interior hA hB hc ht0.le ht x hx
  have he:coleHopf c 0 A=A := funext (coleHopf_zero c A)
  simpa only [R,scaledHeatJet,sub_self,he,←D.evolve_jet h hh,spatialJet] using hhR

lemma ForwardShape.jump {A:ℝ → ℝ} {c d:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape c A) (hc:0<c) (hcd:c≤d) {D:ForwardDensityData}
    (hF:ForwardShape c A D) :
    ForwardShape d A (D.jump hA hB.even (d-c) (sub_nonneg.mpr hcd)) := by
  obtain ⟨hsl,hsc⟩:=D.jump_slope_concavity hA hB.even (d-c) (sub_nonneg.mpr hcd)
    hF.slope hF.concave (by simpa only [iteratedDeriv_one] using fun x ↦ (hB.convex x).le)
    (by
      intro x hx
      have hw:=hB.w x hx
      dsimp only [spatialJet] at hw
      nlinarith)
  refine ⟨hsl,hsc,?_⟩
  intro x hx
  simp only [D.jump_jet,spatialJet]
  have hj:=hF.coupled x hx
  dsimp only [spatialJet] at hj
  have hh:=mul_nonneg (div_nonneg (hc.le.trans hcd) hc.le) hj
  convert! hh using 1; field_simp; ring
end SKValue

end

end OAI
