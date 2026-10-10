import OAI.Analysis.LienardCycles.RadiusSigns

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology
namespace QuinticLienard.RegionBarrier

lemma last_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (ha : f a < 0) (hb : 0 < f b) :
    ∃ c ∈ Ico a b, f c=0 ∧ ∀ t ∈ Ioc c b, 0 < f t := by
  let S := Icc a b ∩ f ⁻¹' {0}
  have hclose : IsClosed S := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcomp : IsCompact S := isCompact_Icc.of_isClosed_subset hclose inter_subset_left
  obtain ⟨x,hx,hx0⟩ := intermediate_value_Icc hab.le hf (show (0:ℝ) ∈ Icc (f a) (f b) from ⟨ha.le,hb.le⟩)
  have hne : S.Nonempty := ⟨x,hx,hx0⟩
  obtain ⟨c,hc,hmax⟩ := hcomp.exists_isMaxOn hne continuousOn_id
  have hc0 : f c=0 := hc.2
  have hcb : c < b := lt_of_le_of_ne hc.1.2 (by intro h; rw [h] at hc0; linarith)
  refine ⟨c,⟨hc.1.1,hcb⟩,hc0,?_⟩
  intro t ht
  by_contra! hnt
  have hft := hf.mono (Icc_subset_Icc (hc.1.1.trans ht.1.le) le_rfl)
  obtain ⟨x,hx,hx0⟩ := intermediate_value_Icc ht.2 hft (show (0:ℝ) ∈ Icc (f t) (f b) from ⟨hnt,hb.le⟩)
  have hxS : x ∈ S := ⟨⟨hc.1.1.trans (ht.1.le.trans hx.1),hx.2⟩,hx0⟩
  have hh := hmax hxS
  exact (ht.1.trans_le hx.1).not_ge hh

lemma no_negative_w_at_positive_slope {h f w C w' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hH : ∀ t ∈ Icc a b, HasDerivAt h (f t) t)
    (hF : ∀ t ∈ Icc a b, HasDerivAt f (C t*w t) t)
    (hW : ∀ t ∈ Icc a b, HasDerivAt w (w' t) t)
    (hC : ∀ t ∈ Icc a b, 0 < C t)
    (hWp : ∀ t ∈ Icc a b, h t < 0 → 0 ≤ f t → 0 < w' t)
    (ha : f a < 0) (hb : h b < 0) (hfb : 0 < f b) : 0 ≤ w b := by
  by_contra! hwb
  obtain ⟨c,hc,hc0,hpos⟩ := last_zero hab
    (fun t ht => (hF t ht).continuousAt.continuousWithinAt) ha hfb
  have hsub : Icc c b ⊆ Icc a b := Icc_subset_Icc hc.1 le_rfl
  have hfn (t : ℝ) (ht : t ∈ Icc c b) : 0 ≤ f t := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h,hc0]
    · exact (hpos t ⟨h,ht.2⟩).le
  have hmH : MonotoneOn h (Icc c b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc c b)
      (fun t ht => (hH t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hH t (hsub (interior_subset ht))).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hH t (hsub (interior_subset ht))).deriv]
    exact hfn t (interior_subset ht)
  have hneg (t : ℝ) (ht : t ∈ Icc c b) : h t < 0 :=
    (hmH ht ⟨hc.2.le,le_rfl⟩ ht.2).trans_lt hb
  have hmW : MonotoneOn w (Icc c b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc c b)
      (fun t ht => (hW t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hW t (hsub (interior_subset ht))).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hW t (hsub (interior_subset ht))).deriv]
    exact (hWp t (hsub (interior_subset ht)) (hneg t (interior_subset ht)) (hfn t (interior_subset ht))).le
  have hmF : StrictAntiOn f (Icc c b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc c b)
      (fun t ht => (hF t (hsub ht)).continuousAt.continuousWithinAt)
    intro t ht
    rw [(hF t (hsub (interior_subset ht))).deriv]
    exact mul_neg_of_pos_of_neg (hC t (hsub (interior_subset ht)))
      ((hmW (interior_subset ht) ⟨hc.2.le,le_rfl⟩ (interior_subset ht).2).trans_lt hwb)
  have hh := hmF ⟨le_rfl,hc.2.le⟩ ⟨hc.2.le,le_rfl⟩ hc.2
  rw [hc0] at hh
  linarith

lemma no_negative_w {h f w C w' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hH : ∀ t ∈ Icc a b, HasDerivAt h (f t) t)
    (hF : ∀ t ∈ Icc a b, HasDerivAt f (C t*w t) t)
    (hW : ∀ t ∈ Icc a b, HasDerivAt w (w' t) t)
    (hC : ∀ t ∈ Icc a b, 0 < C t)
    (hWp : ∀ t ∈ Icc a b, h t < 0 → 0 ≤ f t → 0 < w' t)
    (ha : f a < 0) (hb : h b < 0) (hfb : 0 ≤ f b) : 0 ≤ w b := by
  rcases hfb.eq_or_lt with hfb | hfb
  · by_contra! hwb
    have hbb : b ∈ Icc a b := ⟨hab.le,le_rfl⟩
    have hlim := (hasDerivWithinAt_iff_tendsto_slope' (show b ∉ Iio b by simp)).mp
      ((hF b hbb).hasDerivWithinAt (s := Iio b))
    have hdneg : C b*w b < 0 := mul_neg_of_pos_of_neg (hC b hbb) hwb
    have he : ∀ᶠ t in 𝓝[<] b, a < t ∧ t < b ∧ h t < 0 ∧ w t < 0 ∧ 0 < f t := by
      filter_upwards [(eventually_gt_nhds hab).filter_mono inf_le_left,self_mem_nhdsWithin,
        ((hH b hbb).continuousAt.eventually (eventually_lt_nhds hb)).filter_mono inf_le_left,
        ((hW b hbb).continuousAt.eventually (eventually_lt_nhds hwb)).filter_mono inf_le_left,
        hlim.eventually (eventually_lt_nhds hdneg)] with t hat htb hht hwt hft
      refine ⟨hat,htb,hht,hwt,?_⟩
      have hf0 : f b=0 := hfb.symm
      have hdiv : (f t)/(t-b)<0 := by simpa [slope,vsub_eq_sub,hf0,div_eq_mul_inv,mul_comm] using hft
      have h := (div_lt_iff_of_neg (sub_neg.mpr htb)).mp hdiv
      simpa using h
    obtain ⟨t,hat,htb,hht,hwt,hft⟩ := he.exists
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right htb.le
    exact hwt.not_ge (no_negative_w_at_positive_slope hat
      (fun s hs => hH s (hsub hs)) (fun s hs => hF s (hsub hs))
      (fun s hs => hW s (hsub hs)) (fun s hs => hC s (hsub hs))
      (fun s hs => hWp s (hsub hs)) ha hht hft)
  · exact no_negative_w_at_positive_slope hab hH hF hW hC hWp ha hb hfb
end QuinticLienard.RegionBarrier

end OAI
