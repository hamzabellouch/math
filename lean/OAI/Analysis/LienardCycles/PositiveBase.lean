import OAI.Analysis.LienardCycles.ActualFitLimits

namespace OAI

universe uP

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
namespace QuinticLienard.PositiveWidth
open ScalarArcs ArcEndpoints ArcFamilies PositiveVariation
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
noncomputable def baseAtWidth (q : (P × ℝ) × ℝ) : ℝ :=
  Classical.epsilon (fun h => 0<h ∧ h<q.1.2 ∧ widthFamily Φ ((q.1.1,q.1.2),h)=q.2)
def Admissible (q : (P × ℝ) × ℝ) : Prop :=
  ∃ h, 0<h ∧ h<q.1.2 ∧ widthFamily Φ ((q.1.1,q.1.2),h)=q.2
omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
lemma base_spec {p : P} {t r : ℝ} (he : Admissible Φ ((p,t),r)) :
    0<baseAtWidth Φ ((p,t),r) ∧ baseAtWidth Φ ((p,t),r)<t ∧
    widthFamily Φ ((p,t),baseAtWidth Φ ((p,t),r))=r :=
  Classical.epsilon_spec he
include hΦ hloc
lemma base_eq {p : P} {t h r : ℝ} (hh : 0<h) (hht : h<t)
    (he : widthFamily Φ ((p,t),h)=r) : baseAtWidth Φ ((p,t),r)=h := by
  have hs := base_spec Φ (show Admissible Φ ((p,t),r) from ⟨h,hh,hht,he⟩)
  exact (width_strictAnti_base Φ hΦ hloc p t).injOn ⟨hs.1,hs.2.1⟩ ⟨hh,hht⟩ (hs.2.2.trans he.symm)
lemma base_exists_le {p : P} {t h r : ℝ} (hh : 0<h) (hht : h<t) (hr : 0<r)
    (hle : r≤widthFamily Φ ((p,t),h)) : Admissible Φ ((p,t),r) := by
  have hφ : ContDiffOn ℝ 1 (fun u => Φ (p,u)) (Ioi 0) := by
    intro x hx
    exact (((hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
  obtain ⟨δ,hδ,hsmall⟩ := width_small_base hφ t (hh.trans hht) hr
  let b := t-min δ (t-h)/2
  have hbh : h<b := by dsimp [b]; linarith [min_le_right δ (t-h)]
  have hbt : b<t := by dsimp [b]; linarith [lt_min hδ (sub_pos.mpr hht)]
  have hwb : widthFamily Φ ((p,t),b)<r := hsmall b (by dsimp [b]; linarith [min_le_left δ (t-h)]) hbt
  have hc : ContinuousOn (fun u => widthFamily Φ ((p,t),u)) (Icc h b) := by
    intro u hu
    exact ((width_analytic Φ hΦ hloc (hh.trans_le hu.1) (hu.2.trans_lt hbt)).comp u
      (contDiffAt_const.prodMk contDiffAt_id)).continuousAt.continuousWithinAt
  obtain ⟨u,hu,he⟩ := intermediate_value_Icc' hbh.le hc ⟨hwb.le,hle⟩
  exact ⟨u,hh.trans_le hu.1,hu.2.trans_lt hbt,he⟩
lemma base_local {p : P} {t r : ℝ} (he : Admissible Φ ((p,t),r)) :
    ContDiffAt ℝ ω (baseAtWidth Φ) ((p,t),r) ∧ ∀ᶠ q in 𝓝 ((p,t),r), Admissible Φ q := by
  let h := baseAtWidth Φ ((p,t),r)
  have hs := base_spec Φ he
  have hwd := width_analytic Φ hΦ hloc (p:=p) hs.1 hs.2.1
  have hd := width_base_deriv Φ hΦ hloc (p:=p) hs.1 hs.2.1
  have hdneg : -widthFamily Φ ((p,t),h) /
      ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2) < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos (width_pos Φ hΦ hs.1 hs.2.1)) (gap_pos Φ hΦ hs.1 hs.2.1)
  obtain ⟨Y,hY,hY0,hy⟩ := level_hit hwd hd hs.2.2 hdneg.ne
  have hlt : ∀ᶠ q in 𝓝 ((p,t),r), Y q<q.1.2 :=
    hY.continuousAt.eventually_lt continuousAt_fst.snd (by simpa only [hY0] using hs.2.1)
  have hpos : ∀ᶠ q in 𝓝 ((p,t),r), 0<Y q :=
    continuousAt_const.eventually_lt hY.continuousAt (by simpa only [hY0] using hs.1)
  constructor
  · apply hY.congr_of_eventuallyEq
    filter_upwards [hy,hlt,hpos] with q hq htq hpq
    exact base_eq Φ hΦ hloc hpq htq hq
  · filter_upwards [hy,hlt,hpos] with q hq htq hpq
    exact ⟨Y q,hpq,htq,hq⟩
lemma base_analytic {p : P} {t r : ℝ} (he : Admissible Φ ((p,t),r)) :
    ContDiffAt ℝ ω (baseAtWidth Φ) ((p,t),r) := (base_local Φ hΦ hloc he).1
lemma base_width_deriv {p : P} {t r : ℝ} (he : Admissible Φ ((p,t),r)) :
    HasDerivAt (fun s => baseAtWidth Φ ((p,t),s))
      (-(r^2-(midpointFamily Φ ((p,t),baseAtWidth Φ ((p,t),r)))^2)/r) r := by
  let b : ℝ → ℝ := fun s => baseAtWidth Φ ((p,t),s)
  have hs := base_spec Φ he
  have hb := ((base_analytic Φ hΦ hloc he).comp r
    (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hw := width_base_deriv Φ hΦ hloc (p:=p) hs.1 hs.2.1
  have hc := hw.comp r hb.hasDerivAt
  have hev : (fun s => widthFamily Φ ((p,t),b s)) =ᶠ[𝓝 r] id := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually (base_local Φ hΦ hloc he).2] with s hs
    exact (base_spec Φ hs).2.2
  have heq := (hc.congr_of_eventuallyEq hev.symm).unique (hasDerivAt_id r)
  rw [hs.2.2] at heq
  have hr : 0<r := hs.2.2 ▸ width_pos Φ hΦ hs.1 hs.2.1
  have hg := gap_pos Φ hΦ (p:=p) hs.1 hs.2.1
  rw [hs.2.2] at hg
  convert! hb.hasDerivAt using 1
  field_simp [hr.ne',hg.ne'] at heq ⊢
  nlinarith [heq]
lemma base_midpoint {p : P} {t r : ℝ} (he : Admissible Φ ((p,t),r)) :
    midpointAtWidth Φ ((p,baseAtWidth Φ ((p,t),r)),r)=
      midpointFamily Φ ((p,t),baseAtWidth Φ ((p,t),r)) := by
  have hs := base_spec Φ he
  have hr : 0<r := hs.2.2 ▸ width_pos Φ hΦ hs.1 hs.2.1
  dsimp only [midpointAtWidth]
  rw [peak_eq Φ hΦ hloc hr hs.1 hs.2.1 hs.2.2]
lemma base_tendsto {p : P} {t h : ℝ} (hh : 0<h) (hht : h<t) :
    Tendsto (fun s => baseAtWidth Φ ((p,t),s)) (𝓝[>] (0:ℝ)) (𝓝 t) := by
  have hr := width_pos Φ hΦ (p:=p) hh hht
  have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), Admissible Φ ((p,t),s) := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hr).filter_mono inf_le_left] with s hs hsr
    exact base_exists_le Φ hΦ hloc hh hht hs hsr.le
  have hl : Tendsto (fun s : ℝ => t-s^2/2) (𝓝[>] (0:ℝ)) (𝓝 t) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => t) (𝓝[>] (0:ℝ)) (𝓝 t)).sub
      (((tendsto_id.mono_left inf_le_left : Tendsto (fun s : ℝ => s) (𝓝[>] (0:ℝ)) (𝓝 0)).pow 2).div_const 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [hev] with s hs
    have hb := base_spec Φ hs
    have he := height_bound Φ hΦ hloc (p:=p) hb.1 hb.2.1
    rw [hb.2.2] at he
    linarith
  · filter_upwards [hev] with s hs
    exact (base_spec Φ hs).2.1.le
end QuinticLienard.PositiveWidth

end OAI
