import OAI.Analysis.LienardCycles.Intercept

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScalarArcs
lemma IsArch.endpoint_bounds {φ u : ℝ → ℝ} {h t a b B : ℝ}
    (hu : IsArch φ u h t a b) (hh : 0≤h) (ht : h<t) (hB : 0≤B)
    (hb : ∀ x ∈ Icc h t, |φ x|≤B) :
    -4*(B+t+1)≤a ∧ b≤4*(B+t+1) := by
  have hab := hu.lower_lt_peak.trans hu.peak_lt_upper
  have hct := hb t ⟨ht.le,le_rfl⟩
  have hc : -B≤φ t ∧ φ t≤B := abs_le.mp hct
  have hdp (y : ℝ) (hy : y ∈ Icc a b) :
      HasDerivAt (fun y=>u y+(y-B)^2/2) (φ (u y)-B) y := by
    convert! (hu.equation y hy).add ((((hasDerivAt_id y).sub_const B).pow 2).div_const 2) using 1
    simp only [id_eq]
    ring
  have hdm (y : ℝ) (hy : y ∈ Icc a b) :
      HasDerivAt (fun y=>u y+(y+B)^2/2) (φ (u y)+B) y := by
    convert! (hu.equation y hy).add ((((hasDerivAt_id y).add_const B).pow 2).div_const 2) using 1
    simp only [id_eq]
    ring
  have hmp : AntitoneOn (fun y=>u y+(y-B)^2/2) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (fun y hy=>(hdp y hy).continuousAt.continuousWithinAt)
      (fun y hy=>(hdp y (interior_subset hy)).differentiableAt.differentiableWithinAt)
    intro y hy
    rw [(hdp y (interior_subset hy)).deriv]
    exact sub_nonpos.mpr (abs_le.mp (hb _ (hu.range_mem y (interior_subset hy)))).2
  have hmm : MonotoneOn (fun y=>u y+(y+B)^2/2) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun y hy=>(hdm y hy).continuousAt.continuousWithinAt)
      (fun y hy=>(hdm y (interior_subset hy)).differentiableAt.differentiableWithinAt)
    intro y hy
    rw [(hdm y (interior_subset hy)).deriv]
    have hx := (abs_le.mp (hb _ (hu.range_mem y (interior_subset hy)))).1
    linarith
  have hl := hmm (show a ∈ Icc a b from ⟨le_rfl,hab.le⟩)
    (show φ t ∈ Icc a b from ⟨hu.lower_lt_peak.le,hu.peak_lt_upper.le⟩) hu.lower_lt_peak.le
  have hr := hmp (show φ t ∈ Icc a b from ⟨hu.lower_lt_peak.le,hu.peak_lt_upper.le⟩)
    (show b ∈ Icc a b from ⟨hab.le,le_rfl⟩) hu.peak_lt_upper.le
  dsimp only at hl hr
  rw [hu.lower,hu.peak] at hl
  rw [hu.upper,hu.peak] at hr
  have hsq : (φ t)^2≤B^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hc.2) (show 0≤φ t+B by linarith [hc.1])]
  have hBc : |B*φ t|≤B^2 := by rw [abs_mul,abs_of_nonneg hB,pow_two]; exact mul_le_mul_of_nonneg_left hct hB
  have hBc' := abs_le.mp hBc
  have htl : 0≤t := hh.trans ht.le
  have hBt : 0≤B*t := mul_nonneg hB htl
  constructor
  · by_contra! hn
    have hcomp : (4*(B+t+1)-B)^2<(a+B)^2 := by nlinarith [sq_nonneg (a+B+4*(B+t+1)-B)]
    nlinarith [sq_nonneg t,sq_nonneg B]
  · by_contra! hn
    have hcomp : (4*(B+t+1)-B)^2<(b-B)^2 := by nlinarith [sq_nonneg (b-B-(4*(B+t+1)-B))]
    nlinarith [sq_nonneg t,sq_nonneg B]

lemma lower_strictMono_base {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 1 φ (Ioi 0)) (t : ℝ) :
    StrictMonoOn (fun h=>lower φ h t) (Ioo 0 t) := by
  intro h hh k hk hhk
  have hu := chosen_arch (positive_arch_exists hφ hh.1 hh.2)
  obtain ⟨a,b,ha,_,hab⟩ := hu.subarch_positive hφ hh.1 hhk hk.2
  dsimp only
  rw [(canonical_of_positive_arch hab hφ hk.1 hk.2).1]
  exact ha
lemma upper_strictAnti_base {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 1 φ (Ioi 0)) (t : ℝ) :
    StrictAntiOn (fun h=>upper φ h t) (Ioo 0 t) := by
  intro h hh k hk hhk
  have hu := chosen_arch (positive_arch_exists hφ hh.1 hh.2)
  obtain ⟨a,b,_,hb,hab⟩ := hu.subarch_positive hφ hh.1 hhk hk.2
  dsimp only
  rw [(canonical_of_positive_arch hab hφ hk.1 hk.2).2]
  exact hb

noncomputable def axisLower (φ : ℝ → ℝ) (t : ℝ) : ℝ := sInf ((fun h=>lower φ h t) '' Ioo 0 t)
noncomputable def axisUpper (φ : ℝ → ℝ) (t : ℝ) : ℝ := sSup ((fun h=>upper φ h t) '' Ioo 0 t)
lemma axis_bounded {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hc : ContinuousOn φ (Ici 0)) {t : ℝ} (ht : 0<t) :
    BddBelow ((fun h=>lower φ h t) '' Ioo 0 t) ∧ BddAbove ((fun h=>upper φ h t) '' Ioo 0 t) := by
  obtain ⟨v,hv,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr ht.le)
    (hc.abs.mono (show Icc 0 t ⊆ Ici 0 from fun _ h=>h.1))
  have hb (h : ℝ) (hh : h ∈ Ioo 0 t) :=
    (chosen_arch (positive_arch_exists hφ hh.1 hh.2)).endpoint_bounds hh.1.le hh.2 (abs_nonneg (φ v))
      (fun x hx=>hmax ⟨hh.1.le.trans hx.1,hx.2⟩)
  exact ⟨⟨-4*(|φ v|+t+1),fun x hx=> by obtain ⟨h,hh,rfl⟩:=hx; exact (hb h hh).1⟩,
    ⟨4*(|φ v|+t+1),fun x hx=> by obtain ⟨h,hh,rfl⟩:=hx; exact (hb h hh).2⟩⟩

lemma lower_axis_tendsto {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hc : ContinuousOn φ (Ici 0)) {t : ℝ} (ht : 0<t) :
    Tendsto (fun h=>lower φ h t) (𝓝[>] 0) (𝓝 (axisLower φ t)) := by
  have hb := (axis_bounded hφ hc ht).1
  have hne : ((fun h=>lower φ h t) '' Ioo 0 t).Nonempty :=
    (nonempty_Ioo.mpr ht).image _
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds ht).filter_mono inf_le_left] with h hh hht
    exact ha.trans_le (csInf_le hb (mem_image_of_mem _ ⟨hh,hht⟩))
  · intro b hb'
    obtain ⟨x,hx,hxb⟩ := exists_lt_of_csInf_lt hne hb'
    obtain ⟨k,hk,rfl⟩ := hx
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hk.1).filter_mono inf_le_left] with h hh hhk
    exact ((lower_strictMono_base hφ t) ⟨hh,hhk.trans hk.2⟩ hk hhk).trans hxb
lemma upper_axis_tendsto {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hc : ContinuousOn φ (Ici 0)) {t : ℝ} (ht : 0<t) :
    Tendsto (fun h=>upper φ h t) (𝓝[>] 0) (𝓝 (axisUpper φ t)) := by
  have hb := (axis_bounded hφ hc ht).2
  have hne : ((fun h=>upper φ h t) '' Ioo 0 t).Nonempty :=
    (nonempty_Ioo.mpr ht).image _
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨x,hx,hax⟩ := exists_lt_of_lt_csSup hne ha
    obtain ⟨k,hk,rfl⟩ := hx
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hk.1).filter_mono inf_le_left] with h hh hhk
    exact hax.trans ((upper_strictAnti_base hφ t) ⟨hh,hhk.trans hk.2⟩ hk hhk)
  · intro b hb'
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds ht).filter_mono inf_le_left] with h hh hht
    exact (le_csSup hb (mem_image_of_mem _ ⟨hh,hht⟩)).trans_lt hb'

lemma axis_signs {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hc : ContinuousOn φ (Ici 0)) (h0 : φ 0=0) {t : ℝ} (ht : 0<t) :
    axisLower φ t≤0 ∧ 0≤axisUpper φ t := by
  have hlim : Tendsto φ (𝓝[>] 0) (𝓝 (0:ℝ)) := by
    simpa only [h0] using (hc 0 (show (0:ℝ) ∈ Set.Ici (0:ℝ) by simp)).mono_left (nhdsWithin_mono (0:ℝ) Ioi_subset_Ici_self)
  have he : ∀ᶠ h in 𝓝[>] (0:ℝ), lower φ h t≤φ h ∧ φ h≤upper φ h t := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds ht).filter_mono inf_le_left] with h hh hht
    have hu := chosen_arch (positive_arch_exists hφ hh hht)
    exact ⟨hu.lower_transverse.le,hu.upper_transverse.le⟩
  exact ⟨le_of_tendsto_of_tendsto (lower_axis_tendsto hφ hc ht) hlim (he.mono fun _ h=>h.1),
    le_of_tendsto_of_tendsto hlim (upper_axis_tendsto hφ hc ht) (he.mono fun _ h=>h.2)⟩
end QuinticLienard.ScalarArcs

end OAI
