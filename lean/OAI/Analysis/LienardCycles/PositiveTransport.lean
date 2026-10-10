import OAI.Analysis.LienardCycles.PositiveWidth

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
namespace QuinticLienard.PositiveTransport
open ScalarArcs ArcEndpoints ArcFamilies PositiveVariation PositiveWidth PartialCalculus
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
include hΦ hloc

theorem peak_width_deriv {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    HasDerivAt (fun s => peakAtWidth Φ ((p,h),s))
      (1/deriv (fun t => widthFamily Φ ((p,t),h)) (peakAtWidth Φ ((p,h),r))) r := by
  let t := peakAtWidth Φ ((p,h),r)
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hhpos hr
  let f : ℝ → ℝ := fun t => widthFamily Φ ((p,t),h)
  let g : ℝ → ℝ := fun s => peakAtWidth Φ ((p,h),s)
  have hf : DifferentiableAt ℝ f t :=
    ((width_analytic Φ hΦ hloc hhpos hs.1).comp t
      ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt (by simp)
  have hg : DifferentiableAt ℝ g r :=
    ((peak_analytic Φ hΦ hloc hhpos hr).comp r
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have he : (f ∘ g) =ᶠ[𝓝 r] id := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
    exact (peak_spec Φ hΦ hloc hhpos hs).2
  have hc := (hf.hasDerivAt.comp r hg.hasDerivAt).unique
    ((hasDerivAt_id r).congr_of_eventuallyEq he)
  have hp : 0 < deriv f t := (peak_width_midpoint_bounds Φ hΦ hloc hhpos hs.1).1
  have heq : deriv g r = 1/deriv f t := by
    apply (eq_div_iff hp.ne').mpr
    simpa only [mul_comm] using hc
  simpa only [heq] using hg.hasDerivAt

theorem midpoint_width_deriv_abs_lt {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    |deriv (fun s => midpointAtWidth Φ ((p,h),s)) r| < 1 := by
  let t := peakAtWidth Φ ((p,h),r)
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hhpos hr
  let m : ℝ → ℝ := fun t => midpointFamily Φ ((p,t),h)
  have hm : DifferentiableAt ℝ m t :=
    ((midpoint_analytic Φ hΦ hloc hhpos hs.1).comp t
      ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)).differentiableAt (by simp)
  have hc := hm.hasDerivAt.comp r (peak_width_deriv Φ hΦ hloc hhpos hr)
  have hder : deriv (fun s => midpointAtWidth Φ ((p,h),s)) r =
      deriv m t / deriv (fun t => widthFamily Φ ((p,t),h)) t := by
    simpa only [Function.comp_def,mul_one_div,midpointAtWidth,m,t] using! hc.deriv
  rw [hder]
  exact (peak_width_midpoint_bounds Φ hΦ hloc (p := p) hhpos hs.1).2

theorem midpoint_base_deriv {p : P} {t h : ℝ} (hhpos : 0<h) (hht : h < t) :
    HasDerivAt (fun s => midpointFamily Φ ((p,t),s))
      (midpointFamily Φ ((p,t),h) /
        ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2) -
        deriv (fun u => Φ (p,u)) h) h := by
  obtain ⟨hl,hr⟩ := base_derivatives Φ hΦ hloc (p := p) hhpos hht
  have hφ : ContDiffOn ℝ 1 (fun u => Φ (p,u)) (Ioi 0) := by
    intro x hx
    exact (((hΦ (p,x) hx).comp x (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)).contDiffWithinAt
  have hdφ := (((hΦ (p,h) hhpos).comp h (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)).hasDerivAt
  have hu := chosen_arch (positive_arch_exists hφ hhpos hht)
  have hlne : Φ (p,h)-lowerFamily Φ ((p,t),h) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hu.lower_transverse)
  have hrne : Φ (p,h)-upperFamily Φ ((p,t),h) ≠ 0 :=
    ne_of_lt (sub_neg.mpr hu.upper_transverse)
  have hqne := ne_of_gt (gap_pos Φ hΦ (p := p) hhpos hht)
  have he : (1/(Φ (p,h)-upperFamily Φ ((p,t),h)) +
      1/(Φ (p,h)-lowerFamily Φ ((p,t),h)))/2 =
      midpointFamily Φ ((p,t),h) /
        ((widthFamily Φ ((p,t),h))^2-(midpointFamily Φ ((p,t),h))^2) := by
    apply (eq_div_iff hqne).mpr
    dsimp [widthFamily,midpointFamily,width,ScalarArcs.midpoint,lowerFamily,upperFamily] at *
    field_simp
    ring
  rw [←he]
  exact ((hr.add hl).div_const 2).sub hdφ

noncomputable def M (p : P) (q : ℝ × ℝ) : ℝ := midpointAtWidth Φ ((p,q.1),q.2)
noncomputable def v (p : P) : ℝ × ℝ → ℝ := second (M Φ p)

theorem M_analytic {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    ContDiffAt ℝ ω (M Φ p) (h,r) :=
  (midpointAtWidth_analytic Φ hΦ hloc hhpos hr).comp (h,r)
    ((contDiffAt_const.prodMk contDiffAt_fst).prodMk contDiffAt_snd)

theorem v_analytic {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    ContDiffAt ℝ ω (v Φ p) (h,r) := second_contDiffAt (M_analytic Φ hΦ hloc hhpos hr)

theorem M_abs_lt {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) : |M Φ p (h,r)| < r :=
  midpointAtWidth_abs_lt Φ hΦ hloc hhpos hr

theorem v_abs_lt {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) : |v Φ p (h,r)| < 1 := by
  have he := (second_hasDerivAt ((M_analytic Φ hΦ hloc (p := p) (h := h) hhpos hr).differentiableAt
    (by simp))).deriv
  change deriv (fun s => midpointAtWidth Φ ((p,h),s)) r = v Φ p (h,r) at he
  rw [←he]
  exact midpoint_width_deriv_abs_lt Φ hΦ hloc hhpos hr

theorem M_gap_pos {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) : 0 < r^2-(M Φ p (h,r))^2 :=
  sub_pos.mpr (sq_lt_sq.mpr (by simpa only [abs_of_pos hr] using M_abs_lt Φ hΦ hloc (p := p) (h := h) hhpos hr))

theorem midpoint_reparam {p : P} {h t : ℝ} (hhpos : 0<h) (hht : h < t) :
    M Φ p (h,widthFamily Φ ((p,t),h)) = midpointFamily Φ ((p,t),h) := by
  dsimp [M,midpointAtWidth]
  rw [peak_eq Φ hΦ hloc (width_pos Φ hΦ (p := p) hhpos hht) hhpos hht rfl]

theorem transport_midpoint {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    first (M Φ p) (h,r) - r/(r^2-(M Φ p (h,r))^2)*v Φ p (h,r) =
      M Φ p (h,r)/(r^2-(M Φ p (h,r))^2)-deriv (fun u => Φ (p,u)) h := by
  let t := peakAtWidth Φ ((p,h),r)
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hhpos hr
  have hM := M_analytic Φ hΦ hloc (p := p) (h := h) hhpos hr
  have hw := width_base_deriv Φ hΦ hloc (p := p) hhpos hs.1
  have hm := midpoint_base_deriv Φ hΦ hloc (p := p) hhpos hs.1
  change HasDerivAt (fun s => widthFamily Φ ((p,t),s))
    (-widthFamily Φ ((p,t),h)/(widthFamily Φ ((p,t),h)^2-M Φ p (h,r)^2)) h at hw
  change HasDerivAt (fun s => midpointFamily Φ ((p,t),s))
    (M Φ p (h,r)/(widthFamily Φ ((p,t),h)^2-M Φ p (h,r)^2)-deriv (fun u => Φ (p,u)) h) h at hm
  have hsr := hs.2
  change widthFamily Φ ((p,t),h) = r at hsr
  rw [hsr] at hw hm
  have hMc := hM.differentiableAt (by simp)
  have hMd : HasFDerivAt (M Φ p) (fderiv ℝ (M Φ p) (h,r))
      (h,widthFamily Φ ((p,t),h)) := by simpa only [hsr] using hMc.hasFDerivAt
  have hcomp := hMd.comp_hasDerivAt h ((hasDerivAt_id h).prodMk hw)
  have he : (fun s => M Φ p (s,widthFamily Φ ((p,t),s))) =ᶠ[𝓝 h]
      (fun s => midpointFamily Φ ((p,t),s)) := by
    filter_upwards [continuousAt_id.eventually_lt continuousAt_const (peak_spec Φ hΦ hloc (p := p) (h := h) hhpos hr).1,
      continuousAt_const.eventually_lt continuousAt_id hhpos] with s hs hsp
    exact midpoint_reparam Φ hΦ hloc hsp hs
  have hcoeff := hcomp.unique (hm.congr_of_eventuallyEq he)
  rw [fderiv_pair] at hcoeff
  change first (M Φ p) (h,r) - r/(r^2-M Φ p (h,r)^2)*second (M Φ p) (h,r) = _
  convert hcoeff using 1
  ring

theorem transport_midpoint_cross {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    (r^2-M Φ p (h,r)^2)*first (M Φ p) (h,r) - r*v Φ p (h,r) =
      M Φ p (h,r) - (r^2-M Φ p (h,r)^2)*deriv (fun u => Φ (p,u)) h := by
  have ht := transport_midpoint Φ hΦ hloc (p := p) (h := h) hhpos hr
  have hq := ne_of_gt (M_gap_pos Φ hΦ hloc (p := p) (h := h) hhpos hr)
  field_simp [hq] at ht
  nlinarith [ht]

theorem transport_v {p : P} {h r : ℝ} (hhpos : 0<h) (hr : 0 < r) :
    first (v Φ p) (h,r) - r/(r^2-M Φ p (h,r)^2)*second (v Φ p) (h,r) =
      -2*M Φ p (h,r)*r*(1-v Φ p (h,r)^2)/(r^2-M Φ p (h,r)^2)^2 := by
  have hMa := M_analytic Φ hΦ hloc (p := p) (h := h) hhpos hr
  have hMd := second_hasDerivAt (hMa.differentiableAt (by simp))
  change HasDerivAt (fun s => M Φ p (h,s)) (v Φ p (h,r)) r at hMd
  have hvd := second_hasDerivAt ((v_analytic Φ hΦ hloc (p := p) (h := h) hhpos hr).differentiableAt (by simp))
  have hfd := second_hasDerivAt ((first_contDiffAt hMa).differentiableAt (by simp))
  rw [←mixed_comm hMa] at hfd
  change HasDerivAt (fun s => first (M Φ p) (h,s)) (first (v Φ p) (h,r)) r at hfd
  have hqd : HasDerivAt (fun s => s^2-M Φ p (h,s)^2)
      (2*r-2*M Φ p (h,r)*v Φ p (h,r)) r := by
    simpa using! ((hasDerivAt_id r).pow 2).sub (hMd.pow 2)
  have hleft := (hqd.mul hfd).sub ((hasDerivAt_id r).mul hvd)
  have hright := hMd.sub (hqd.mul_const (deriv (fun u => Φ (p,u)) h))
  have he : (fun s => (s^2-M Φ p (h,s)^2)*first (M Φ p) (h,s)-s*v Φ p (h,s))
      =ᶠ[𝓝 r] (fun s => M Φ p (h,s)-(s^2-M Φ p (h,s)^2)*deriv (fun u => Φ (p,u)) h) := by
    filter_upwards [continuousAt_const.eventually_lt continuousAt_id hr] with s hs
    exact transport_midpoint_cross Φ hΦ hloc hhpos hs
  have hc := hleft.unique (hright.congr_of_eventuallyEq he)
  have ht := transport_midpoint_cross Φ hΦ hloc (p := p) (h := h) hhpos hr
  have hq := ne_of_gt (M_gap_pos Φ hΦ hloc (p := p) (h := h) hhpos hr)
  dsimp only [id] at hc
  field_simp [hq]
  linear_combination (r^2-M Φ p (h,r)^2)*hc -
    (2*r-2*M Φ p (h,r)*v Φ p (h,r))*ht

end QuinticLienard.PositiveTransport

end OAI
