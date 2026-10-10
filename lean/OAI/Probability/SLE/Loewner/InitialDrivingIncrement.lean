import OAI.Probability.SLE.Loewner.InitialDrivingBound
import OAI.Probability.SLE.Loewner.FutureCapacityAdditive

namespace OAI

/-! A small mapped future slit forces its two driving values to be
close, without any assumed continuity of the driver. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

theorem initialDriving_increment_bound (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1) {R : ℝ} (hR : 0<R)
    (hp : ∀ u : unitInterval, ‖centeredFutureArc p hi h0 hH hst ht u‖<R) :
    |initialDrivingValue p hi h0 hH t ht-
      initialDrivingValue p hi h0 hH s (hst.trans ht)|≤(512*Real.pi+9)*R := by
  let U := initialDrivingValue p hi h0 hH s (hst.trans ht)
  let Q := futureSlitChart p hi h0 hH hst ht
  let w (r : ℝ) := initialForwardChart p hi h0 hH s (p (slitFutureParameter t r))-(U:ℂ)
  have hpt := point_after_prefix_mem_domain p hi hH hst
  have hopen : IsOpen (upperHalfPlane \ range (initialSubarc p s)) :=
    isOpen_upperHalfPlane.sdiff (isCompact_range (initialSubarc p s).continuous).isClosed
  have hG := ((initialForwardChart_differentiableOn_current p hi h0 hH s).differentiableAt
    (hopen.mem_nhds hpt)).continuousAt
  have hf : Tendsto (fun r : ℝ => p (slitFutureParameter t r)) (𝓝 0) (𝓝 (p t)) := by
    have hcont : Continuous (fun r : ℝ => p (slitFutureParameter t r)) :=
      p.continuous.comp (slitFutureParameter_continuous t)
    simpa only [slitFutureParameter_zero] using hcont.tendsto 0
  have hwlim : Tendsto w (𝓝 0) (𝓝 (centeredFutureArc p hi h0 hH hst ht 1)) := by
    have hh := (hG.tendsto.comp hf).sub_const (U:ℂ)
    have he : centeredFutureArc p hi h0 hH hst ht 1=
        initialForwardChart p hi h0 hH s (p t)-(U:ℂ) := by
      change mappedFutureArc p hi h0 hH hst ht 1-(U:ℂ)=_
      rw [mappedFutureArc_segment p hi h0 hH hst ht one_ne_zero,slitSegmentParameter_one]
    rwa [he]
  have hnorm : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖w r‖<2*R := by
    exact (hwlim.norm.eventually (gt_mem_nhds ((hp 1).trans (by linarith)))).filter_mono inf_le_left
  have hl := ((initialDrivingValue_spec p hi h0 hH t ht).sub_const (U:ℂ)).norm
  have hl' : Tendsto (fun r : ℝ => ‖initialForwardChart p hi h0 hH t
      (p (slitFutureParameter t r))-(U:ℂ)‖) (𝓝[>] 0)
      (𝓝 |initialDrivingValue p hi h0 hH t ht-U|) := by
    simpa only [←ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hl
  apply le_of_tendsto hl'
  have hd : 0<1-(t:ℝ) := sub_pos.mpr ht
  filter_upwards [self_mem_nhdsWithin,hnorm,
    Filter.Eventually.filter_mono inf_le_left (gt_mem_nhds hd)] with r hr hwr hrd
  have hz := slitFuturePoint_mem_domain p hi hH t (show r∈Ioo 0 (1-(t:ℝ)) from ⟨hr,hrd⟩)
  have hw := (initialForward_centered_bijOn p hi h0 hH hst ht).mapsTo hz
  have hb := Q.forward_uniform_near
    (centeredFutureArc_injective p hi h0 hH hst ht)
    (centeredFutureArc_zero p hi h0 hH hst ht)
    (fun _ hu => centeredFutureArc_upper p hi h0 hH hst ht hu) hR hp hw hwr.le
  have he : (U:ℂ)+Q.forward (w r)=initialForwardChart p hi h0 hH t
      (p (slitFutureParameter t r)) := futureComposedForward_eq p hi h0 hH hst ht hz
  have he' : Q.forward (w r)=initialForwardChart p hi h0 hH t
      (p (slitFutureParameter t r))-(U:ℂ) := by linear_combination he
  rwa [he'] at hb

end SLEExactGauge

end

end OAI
