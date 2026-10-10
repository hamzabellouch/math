import OAI.Analysis.LienardCycles.PositiveVariation

namespace OAI

universe uP

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.PositiveWidth
open ScalarArcs ArcEndpoints ArcFamilies PositiveVariation

theorem width_small_base {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 1 φ (Ioi 0)) (t : ℝ) (ht : 0<t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h, t-δ < h → h < t → width φ h t < ε := by
  obtain ⟨u,a,b,hu⟩ := positive_arch_exists hφ (show 0<t/2 by linarith) (show t/2<t by linarith)
  let d := min (ε/2) (min ((φ t-a)/2) ((b-φ t)/2))
  have hd : 0 < d := lt_min (by linarith) (lt_min (by linarith [hu.lower_lt_peak])
    (by linarith [hu.peak_lt_upper]))
  have hdε : d ≤ ε/2 := min_le_left _ _
  have hda : d ≤ (φ t-a)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdb : d ≤ (b-φ t)/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hleft : φ t-d ∈ Icc a (φ t) := by constructor <;> linarith [hu.lower_lt_peak]
  have hright : φ t+d ∈ Icc (φ t) b := by constructor <;> linarith [hu.peak_lt_upper]
  have hutl : u (φ t-d) < t := by
    simpa only [hu.peak] using hu.inc hleft ⟨hu.lower_lt_peak.le,le_rfl⟩ (by linarith)
  have hutr : u (φ t+d) < t := by
    simpa only [hu.peak] using hu.dec ⟨le_rfl,hu.peak_lt_upper.le⟩ hright (by linarith)
  let H := max (t/2) (max (u (φ t-d)) (u (φ t+d)))
  have hH : H < t := max_lt (by linarith) (max_lt hutl hutr)
  refine ⟨t-H,sub_pos.mpr hH,?_⟩
  intro h hh hht
  have hHh : H < h := by linarith
  have h₀ : t/2 < h := (le_max_left _ _).trans_lt hHh
  have hlh : u (φ t-d) < h :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hHh
  have hrh : u (φ t+d) < h :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hHh
  obtain ⟨l,r,hal,hrb,hv⟩ := hu.subarch_positive hφ (show 0<t/2 by linarith) h₀ hht
  have hl : φ t-d < l := by
    by_contra hn
    have hh := hu.inc.monotoneOn ⟨hal.le,hv.lower_lt_peak.le⟩ hleft (le_of_not_gt hn)
    rw [hv.lower] at hh
    exact (not_le_of_gt hlh) hh
  have hr : r < φ t+d := by
    by_contra hn
    have hh := hu.dec.antitoneOn hright ⟨hv.peak_lt_upper.le,hrb.le⟩ (le_of_not_gt hn)
    rw [hv.upper] at hh
    exact (not_le_of_gt hrh) hh
  obtain ⟨heql,heqr⟩ := canonical_of_positive_arch hv hφ (by linarith) hht
  dsimp [width]
  rw [heql,heqr]
  linarith

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)

noncomputable def widthFamily (q : (P × ℝ) × ℝ) : ℝ :=
  width (fun u => Φ (q.1.1,u)) q.2 q.1.2
noncomputable def midpointFamily (q : (P × ℝ) × ℝ) : ℝ :=
  midpoint (fun u => Φ (q.1.1,u)) q.2 q.1.2

include hΦ hloc

theorem width_analytic {p : P} {t h : ℝ} (hhpos : 0<h) (hht : h < t) :
    ContDiffAt ℝ ω (widthFamily Φ) ((p,t),h) := by
  obtain ⟨hl,hr⟩ := endpoints Φ hΦ hloc (p := p) hhpos hht
  exact (hr.sub hl).div_const 2

theorem midpoint_analytic {p : P} {t h : ℝ} (hhpos : 0<h) (hht : h < t) :
    ContDiffAt ℝ ω (midpointFamily Φ) ((p,t),h) := by
  obtain ⟨hl,hr⟩ := endpoints Φ hΦ hloc (p := p) hhpos hht
  exact ((hr.add hl).div_const 2).sub
    ((hΦ (p,h) hhpos).comp ((p,t),h) (contDiffAt_fst.fst.prodMk contDiffAt_snd))

omit hloc [FiniteDimensional ℝ P] in
theorem width_pos {p : P} {t h : ℝ} (hhpos : 0<h) (hht : h < t) :
    0 < widthFamily Φ ((p,t),h) := by
  have hφ : ContDiffOn ℝ 1 (fun u => Φ (p,u)) (Ioi 0) := by
    intro x hx
    exact (((hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
  have hu := chosen_arch (positive_arch_exists hφ hhpos hht)
  dsimp [widthFamily,width]
  linarith [hu.lower_lt_peak,hu.peak_lt_upper]

omit hloc [FiniteDimensional ℝ P] in
theorem gap_pos {p : P} {t h : ℝ} (hhpos : 0<h) (hht : h < t) :
    0 < (widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2 := by
  have hφ : ContDiffOn ℝ 1 (fun u => Φ (p,u)) (Ioi 0) := by
    intro x hx
    exact (((hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
  have hb := midpoint_abs_lt_width (positive_arch_exists hφ hhpos hht)
  have ha := width_pos Φ hΦ (p := p) hhpos hht
  change |midpointFamily Φ ((p,t),h)| < widthFamily Φ ((p,t),h) at hb
  exact sub_pos.mpr (sq_lt_sq.mpr (by simpa only [abs_of_pos ha] using hb))

theorem width_base_deriv {p : P} {t h : ℝ} (hhpos : 0<h) (hht : h < t) :
    HasDerivAt (fun s => widthFamily Φ ((p,t),s))
      (-widthFamily Φ ((p,t),h) /
        ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2)) h := by
  obtain ⟨hl,hr⟩ := base_derivatives Φ hΦ hloc (p := p) hhpos hht
  have hφ : ContDiffOn ℝ 1 (fun u => Φ (p,u)) (Ioi 0) := by
    intro x hx
    exact (((hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
  have hu := chosen_arch (positive_arch_exists hφ hhpos hht)
  have hlne : Φ (p,h)-lowerFamily Φ ((p,t),h) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hu.lower_transverse)
  have hrne : Φ (p,h)-upperFamily Φ ((p,t),h) ≠ 0 :=
    ne_of_lt (sub_neg.mpr hu.upper_transverse)
  have hqne := ne_of_gt (gap_pos Φ hΦ (p := p) hhpos hht)
  have he : (1/(Φ (p,h)-upperFamily Φ ((p,t),h)) -
      1/(Φ (p,h)-lowerFamily Φ ((p,t),h)))/2 =
      -widthFamily Φ ((p,t),h) /
        ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2) := by
    apply (eq_div_iff hqne).mpr
    dsimp [widthFamily,midpointFamily,width,ScalarArcs.midpoint,lowerFamily,upperFamily] at *
    field_simp
    ring
  rw [←he]
  exact (hr.sub hl).div_const 2

theorem height_energy_antitone (p : P) (t : ℝ) :
    AntitoneOn (fun h => (widthFamily Φ ((p,t),h))^2+2*h) (Ioo 0 t) := by
  let f : ℝ → ℝ := fun h => (widthFamily Φ ((p,t),h))^2+2*h
  have hd (h : ℝ) (hh : h ∈ Ioo 0 t) : HasDerivAt f
      (2*widthFamily Φ ((p,t),h)*(-widthFamily Φ ((p,t),h) /
        ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2))+2) h := by
    simpa [f] using! ((width_base_deriv Φ hΦ hloc (p:=p) hh.1 hh.2).pow 2).add
      ((hasDerivAt_id h).const_mul 2)
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 t)
    (fun h hh => (hd h hh).continuousAt.continuousWithinAt)
    (fun h hh => (hd h (interior_subset hh)).differentiableAt.differentiableWithinAt)
  intro h hh
  have hh' : h ∈ Ioo 0 t := interior_subset hh
  rw [(hd h hh').deriv]
  have hq := gap_pos Φ hΦ (p:=p) hh'.1 hh'.2
  have he : 2*widthFamily Φ ((p,t),h)*(-widthFamily Φ ((p,t),h) /
        ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2))+2 =
      -(2*(midpointFamily Φ ((p,t),h))^2)/
        ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2) := by
    field_simp
    ring
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (by norm_num) (sq_nonneg _))) hq.le

theorem height_bound {p : P} {t h : ℝ} (hhpos : 0<h) (hht : h<t) :
    2*(t-h) ≤ (widthFamily Φ ((p,t),h))^2 := by
  have ha := height_energy_antitone Φ hΦ hloc p t
  by_contra hn
  have hw := sq_nonneg (widthFamily Φ ((p,t),h))
  let H := ((widthFamily Φ ((p,t),h))^2/2+h+t)/2
  have hH : h<H := by dsimp [H]; linarith
  have hHt : H<t := by dsimp [H]; linarith
  have hle := ha ⟨hhpos,hht⟩ ⟨hhpos.trans hH,hHt⟩ hH.le
  have hW := sq_nonneg (widthFamily Φ ((p,t),H))
  dsimp [H] at hle hW
  linarith

theorem width_strictAnti_base (p : P) (t : ℝ) :
    StrictAntiOn (fun h => widthFamily Φ ((p,t),h)) (Ioo 0 t) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 t)
    (fun h hh => (width_base_deriv Φ hΦ hloc hh.1 hh.2).continuousAt.continuousWithinAt)
  intro h hh
  have hh' : h ∈ Ioo 0 t := interior_subset hh
  rw [(width_base_deriv Φ hΦ hloc (p:=p) hh'.1 hh'.2).deriv]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (width_pos Φ hΦ (p:=p) hh'.1 hh'.2))
    (gap_pos Φ hΦ (p:=p) hh'.1 hh'.2)

theorem width_strictMono_peak (p : P) (h : ℝ) (hhpos : 0<h) :
    StrictMonoOn (fun t => widthFamily Φ ((p,t),h)) (Ioi h) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi h)
  · intro t ht
    exact ((width_analytic Φ hΦ hloc hhpos ht).comp t
      ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).continuousAt.continuousWithinAt
  · intro t ht
    exact (peak_width_midpoint_bounds Φ hΦ hloc (p:=p) hhpos (interior_subset ht)).1

theorem small_peak_exists (p : P) (h : ℝ) (hhpos : 0<h) {ε : ℝ} (hε : 0<ε) :
    ∃ t>h, widthFamily Φ ((p,t),h)<ε := by
  have hφ : ContDiffOn ℝ 1 (fun u => Φ (p,u)) (Ioi 0) := by
    intro x hx
    exact (((hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
  obtain ⟨δ,hδ,hsmall⟩ := width_small_base hφ h hhpos hε
  let b := h-min δ h/2
  have hbh : b<h := by dsimp [b]; linarith [lt_min hδ hhpos]
  have hbpos : 0<b := by dsimp [b]; linarith [min_le_right δ h]
  have hwb : widthFamily Φ ((p,h),b)<ε := hsmall b (by dsimp [b]; linarith [min_le_left δ h]) hbh
  have hg : ContinuousAt (fun t : ℝ => ((p,t),b)) h :=
    (continuousAt_const.prodMk continuousAt_id).prodMk continuousAt_const
  have hc : ContinuousAt (fun t => widthFamily Φ ((p,t),b)) h :=
    ContinuousAt.comp (f:=fun t : ℝ => ((p,t),b)) (g:=widthFamily Φ)
      (width_analytic Φ hΦ hloc (p:=p) hbpos hbh).continuousAt hg
  obtain ⟨η,hη,hnear⟩ := Metric.eventually_nhds_iff.mp (hc.eventually_lt continuousAt_const hwb)
  let t := h+η/2
  have hht : h<t := by dsimp [t]; linarith
  have hsmallt : widthFamily Φ ((p,t),b)<ε :=
    hnear (by rw [Real.dist_eq]; dsimp [t]; rw [abs_of_pos (by linarith)]; linarith)
  exact ⟨t,hht,((width_strictAnti_base Φ hΦ hloc p t)
    ⟨hbpos,hbh.trans hht⟩ ⟨hhpos,hht⟩ hbh).trans hsmallt⟩

theorem peak_exists (p : P) (h : ℝ) (hhpos : 0<h) {r : ℝ} (hr : 0 < r) :
    ∃! t, h < t ∧ widthFamily Φ ((p,t),h) = r := by
  obtain ⟨a,ha,har⟩ := small_peak_exists Φ hΦ hloc p h hhpos hr
  let b := a+r^2+1
  have hab : a < b := by dsimp [b]; nlinarith [sq_nonneg r]
  have hhb : h < b := ha.trans hab
  have hbr : r < widthFamily Φ ((p,b),h) := by
    have hb := height_bound Φ hΦ hloc (p := p) hhpos hhb
    have hw := width_pos Φ hΦ (p := p) hhpos hhb
    dsimp [b] at hb
    nlinarith
  have hc : ContinuousOn (fun t => widthFamily Φ ((p,t),h)) (Icc a b) := by
    intro t ht
    exact ((width_analytic Φ hΦ hloc hhpos (ha.trans_le ht.1)).comp t
      ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).continuousAt.continuousWithinAt
  obtain ⟨t,ht,htr⟩ := intermediate_value_Icc hab.le hc ⟨har.le,hbr.le⟩
  refine ⟨t,⟨ha.trans_le ht.1,htr⟩,?_⟩
  intro s hs
  exact (width_strictMono_peak Φ hΦ hloc p h hhpos).injOn hs.1 (ha.trans_le ht.1)
    (hs.2.trans htr.symm)

noncomputable def peakAtWidth (q : (P × ℝ) × ℝ) : ℝ :=
  Classical.epsilon (fun t => q.1.2 < t ∧ widthFamily Φ ((q.1.1,t),q.1.2) = q.2)

theorem peak_spec {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    h < peakAtWidth Φ ((p,h),r) ∧
      widthFamily Φ ((p,peakAtWidth Φ ((p,h),r)),h) = r :=
  Classical.epsilon_spec (peak_exists Φ hΦ hloc p h hhpos hr).exists

theorem peak_eq {p : P} {h r t : ℝ} (hr : 0 < r) (hhpos : 0<h) (hht : h < t)
    (he : widthFamily Φ ((p,t),h) = r) : peakAtWidth Φ ((p,h),r) = t := by
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hhpos hr
  exact (width_strictMono_peak Φ hΦ hloc p h hhpos).injOn hs.1 hht (hs.2.trans he.symm)

theorem peak_analytic {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    ContDiffAt ℝ ω (peakAtWidth Φ) ((p,h),r) := by
  let t := peakAtWidth Φ ((p,h),r)
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hhpos hr
  let W : (P × ℝ) × ℝ → ℝ := fun q => widthFamily Φ ((q.1.1,q.2),q.1.2)
  have hwd : ContDiffAt ℝ ω W ((p,h),t) :=
    (width_analytic Φ hΦ hloc hhpos hs.1).comp ((p,h),t)
      ((contDiffAt_fst.fst.prodMk contDiffAt_snd).prodMk contDiffAt_fst.snd)
  have hwtd : DifferentiableAt ℝ (fun s => W ((p,h),s)) t :=
    (hwd.comp t (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hdpos : 0 < deriv (fun s => W ((p,h),s)) t :=
    (peak_width_midpoint_bounds Φ hΦ hloc hhpos hs.1).1
  obtain ⟨Y,hY,hY0,he⟩ := level_hit hwd hwtd.hasDerivAt hs.2 hdpos.ne'
  have hlt : ∀ᶠ q in 𝓝 ((p,h),r), q.1.2 < Y q :=
    continuousAt_fst.snd.eventually_lt hY.continuousAt (by simpa only [hY0] using hs.1)
  have hpos : ∀ᶠ q : (P × ℝ) × ℝ in 𝓝 ((p,h),r), 0 < q.2 :=
    continuousAt_const.eventually_lt continuousAt_snd hr
  have hbase : ∀ᶠ q : (P × ℝ) × ℝ in 𝓝 ((p,h),r), 0<q.1.2 :=
    continuousAt_const.eventually_lt continuousAt_fst.snd hhpos
  apply hY.congr_of_eventuallyEq
  filter_upwards [he,hlt,hpos,hbase] with q hq hltq hposq hbq
  exact peak_eq Φ hΦ hloc hposq hbq hltq hq

noncomputable def midpointAtWidth (q : (P × ℝ) × ℝ) : ℝ :=
  midpointFamily Φ ((q.1.1,peakAtWidth Φ q),q.1.2)

theorem midpointAtWidth_analytic {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    ContDiffAt ℝ ω (midpointAtWidth Φ) ((p,h),r) := by
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hhpos hr
  exact (midpoint_analytic Φ hΦ hloc hhpos hs.1).comp ((p,h),r)
    ((contDiffAt_fst.fst.prodMk (peak_analytic Φ hΦ hloc hhpos hr)).prodMk contDiffAt_fst.snd)

theorem midpointAtWidth_abs_lt {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    |midpointAtWidth Φ ((p,h),r)| < r := by
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hhpos hr
  have hφ : ContDiffOn ℝ 1 (fun u => Φ (p,u)) (Ioi 0) := by
    intro x hx
    exact (((hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
  have hb := midpoint_abs_lt_width (positive_arch_exists hφ hhpos hs.1)
  change |midpointAtWidth Φ ((p,h),r)| < widthFamily Φ ((p,peakAtWidth Φ ((p,h),r)),h) at hb
  rwa [hs.2] at hb

end QuinticLienard.PositiveWidth

end OAI
