import OAI.Analysis.LienardCycles.ActualFitTransport

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology
namespace QuinticLienard.ScalarComparison

lemma weighted_deriv {a E F : ℝ → ℝ} {l r : ℝ} (hlr : l≤r)
    (ha : ContinuousOn a (Icc l r)) :
    ∃ w : ℝ → ℝ, (∀ s, 0<w s) ∧ w l=1 ∧
      ∀ s ∈ Icc l r, HasDerivAt E (-a s*E s+F s) s →
        HasDerivAt (fun s=>w s*E s) (w s*F s) s := by
  let ac : ℝ → ℝ := fun s => a (projIcc l r hlr s)
  have hc : Continuous ac := (continuousOn_iff_continuous_domRestrict.mp ha).comp continuous_projIcc
  let w : ℝ → ℝ := fun s => Real.exp (∫ u in l..s,ac u)
  refine ⟨w,fun s=>Real.exp_pos _,by simp [w],?_⟩
  intro s hs hd
  have hh := ((hc.integral_hasStrictDerivAt l s).hasDerivAt.exp).mul hd
  have he : ac s=a s := by simp only [ac,projIcc_of_mem hlr hs]
  rw [he] at hh
  convert! hh using 1
  dsimp only [w]
  ring
lemma linear_pos {a E F : ℝ → ℝ} {l r : ℝ} (hlr : l<r)
    (ha : ContinuousOn a (Icc l r))
    (hd : ∀ s ∈ Icc l r, HasDerivAt E (-a s*E s+F s) s)
    (hF : ∀ s ∈ Ioo l r, 0<F s) (hE : 0≤E l) : 0<E r := by
  obtain ⟨w,hw,hw0,hwd⟩ := weighted_deriv hlr.le ha
  have hm : StrictMonoOn (fun s=>w s*E s) (Icc l r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun s hs => (hwd s hs (hd s hs)).continuousAt.continuousWithinAt)
    intro s hs
    rw [interior_Icc] at hs
    rw [(hwd s ⟨hs.1.le,hs.2.le⟩ (hd s ⟨hs.1.le,hs.2.le⟩)).deriv]
    exact mul_pos (hw s) (hF s hs)
  have hp := hm ⟨le_rfl,hlr.le⟩ ⟨hlr.le,le_rfl⟩ hlr
  dsimp only at hp
  rw [hw0,one_mul] at hp
  exact (mul_pos_iff_of_pos_left (hw r)).mp (hE.trans_lt hp)
lemma linear_pos_of_nonneg {a E F : ℝ → ℝ} {l r : ℝ} (hlr : l≤r)
    (ha : ContinuousOn a (Icc l r))
    (hd : ∀ s ∈ Icc l r, HasDerivAt E (-a s*E s+F s) s)
    (hF : ∀ s ∈ Ioo l r, 0≤F s) (hE : 0<E l) : 0<E r := by
  obtain ⟨w,hw,hw0,hwd⟩ := weighted_deriv hlr ha
  have hm : MonotoneOn (fun s=>w s*E s) (Icc l r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun s hs => (hwd s hs (hd s hs)).continuousAt.continuousWithinAt)
      (fun s hs => (hwd s (interior_subset hs) (hd s (interior_subset hs))).differentiableAt.differentiableWithinAt)
    intro s hs
    rw [interior_Icc] at hs
    rw [(hwd s ⟨hs.1.le,hs.2.le⟩ (hd s ⟨hs.1.le,hs.2.le⟩)).deriv]
    exact mul_nonneg (hw s).le (hF s hs)
  have hp := hm ⟨le_rfl,hlr⟩ ⟨hlr,le_rfl⟩ hlr
  dsimp only at hp
  rw [hw0,one_mul] at hp
  exact (mul_pos_iff_of_pos_left (hw r)).mp (hE.trans_le hp)

lemma linear_negative_from_zero {a E F : ℝ → ℝ} {r : ℝ} (hr : 0<r)
    (ha : ContinuousOn a (Ioc 0 r)) (hap : ∀ s ∈ Ioc 0 r, 0<a s)
    (hd : ∀ s ∈ Ioc 0 r, HasDerivAt E (-a s*E s+F s) s)
    (hF : ∀ s ∈ Ioo 0 r, F s<0)
    (h0 : Tendsto E (𝓝[>] (0:ℝ)) (𝓝 0)) : E r<0 := by
  have hn (s : ℝ) (hs : s ∈ Ioc 0 r) : E s≤0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hev : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0<δ ∧ δ<s ∧ E δ<ε := by
      filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hs.1).filter_mono inf_le_left,
        h0.eventually (eventually_lt_nhds hε)] with δ hδ hδs hEδ
      exact ⟨hδ,hδs,hEδ⟩
    obtain ⟨δ,hδ,hδs,hEδ⟩ := hev.exists
    have hsub : Icc δ s ⊆ Ioc 0 r := fun _ ht=>⟨hδ.trans_le ht.1,ht.2.trans hs.2⟩
    have hb := image_le_of_deriv_right_lt_deriv_boundary
      (fun x hx => (hd x (hsub hx)).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (hsub ⟨hx.1,hx.2.le⟩)).hasDerivWithinAt)
      (B:=fun _=>ε) (B':=fun _=>0) hEδ.le (fun x=>hasDerivAt_const x ε) (by
        intro x hx he
        have hax := hap x (hsub ⟨hx.1,hx.2.le⟩)
        have hfx := hF x ⟨hδ.trans_le hx.1,hx.2.trans_le hs.2⟩
        rw [he]
        nlinarith [mul_pos hax hε]) (show s ∈ Icc δ s from ⟨hδs.le,le_rfl⟩)
    simpa only [zero_add] using hb
  have he := linear_pos (a:=a) (E:=fun s=>-E s) (F:=fun s=>-F s)
    (show r/2<r by linarith)
    (ha.mono (fun s hs=>⟨(half_pos hr).trans_le hs.1,hs.2⟩))
    (fun s hs=>by
      convert! (hd s ⟨(half_pos hr).trans_le hs.1,hs.2⟩).neg using 1
      ring)
    (fun s hs=>neg_pos.mpr (hF s ⟨(half_pos hr).trans hs.1,hs.2⟩))
    (neg_nonneg.mpr (hn (r/2) ⟨half_pos hr,by linarith⟩))
  exact neg_pos.mp he

lemma error_negative_before {a b c E : ℝ → ℝ} {κ r : ℝ} (_hr : 0<r)
    (ha : ContinuousOn a (Ioc 0 r)) (hap : ∀ s ∈ Ioc 0 r,0<a s)
    (hb : ∀ s ∈ Ioc 0 r,0<b s) (hc : StrictAntiOn c (Ioc 0 r))
    (hd : ∀ s ∈ Ioc 0 r,HasDerivAt E (-a s*E s-b s*(c s-κ)) s)
    (h0 : Tendsto E (𝓝[>] (0:ℝ)) (𝓝 0)) (hEr : E r≤0)
    {s : ℝ} (hs : 0<s) (hsr : s<r) : E s<0 := by
  by_cases hcs : κ≤c s
  · apply linear_negative_from_zero hs (ha.mono (Ioc_subset_Ioc_right hsr.le)) (fun x hx=>hap x ⟨hx.1,hx.2.trans hsr.le⟩)
      (F:=fun x=>-b x*(c x-κ))
      (fun x hx=>by simpa only [sub_eq_add_neg,neg_mul] using hd x ⟨hx.1,hx.2.trans hsr.le⟩)
      _ h0
    intro x hx
    have hcx := hc ⟨hx.1,hx.2.le.trans hsr.le⟩ ⟨hs,hsr.le⟩ hx.2
    have hbx := hb x ⟨hx.1,hx.2.le.trans hsr.le⟩
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hbx) (sub_pos.mpr (hcs.trans_lt hcx))
  · by_contra! hEs
    have hp := linear_pos (a:=a) (E:=E) (F:=fun x=>-b x*(c x-κ)) hsr
      (ha.mono (fun x hx=>⟨hs.trans_le hx.1,hx.2⟩))
      (fun x hx=>by simpa only [sub_eq_add_neg,neg_mul] using hd x ⟨hs.trans_le hx.1,hx.2⟩)
      (fun x hx=>by
        have hcx := hc ⟨hs,hsr.le⟩ ⟨hs.trans hx.1,hx.2.le⟩ hx.1
        have hbx := hb x ⟨hs.trans hx.1,hx.2.le⟩
        have hck : c x<κ := hcx.trans (lt_of_not_ge hcs)
        exact mul_pos_of_neg_of_neg (neg_neg_of_pos hbx) (sub_neg.mpr hck)) hEs
    exact (not_lt_of_ge hEr) hp
end QuinticLienard.ScalarComparison

end OAI
