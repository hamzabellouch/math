import OAI.Probability.SLE.Gauge.RestrictedConformalSausage
import OAI.Probability.SLE.Geometry.NormalizedConformalBounds
import OAI.Probability.SLE.Gauge.SerpentineLayout

namespace OAI

/-! A common small displaced experiment disk in normalized half-plane
coordinates. Its nearby trace witnesses stay in a controlled conformal
patch, and its image stays in one physical conformal-radius disk. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge.Serpentine

def conformalExperimentScale (s C : ℝ) : ℝ := min (s / 10) (s / (100 * C))

lemma conformalExperimentScale_bounds {s C : ℝ} (hs : 0 < s) (hC : 0 < C) :
    0 < conformalExperimentScale s C ∧ conformalExperimentScale s C ≤ s / 10 ∧
      C * conformalExperimentScale s C ≤ s / 100 := by
  refine ⟨lt_min (by positivity) (by positivity), min_le_left _ _, ?_⟩
  have hh := (le_div_iff₀ (by positivity : 0 < 100 * C)).mp
    (min_le_right (s / 10) (s / (100 * C)))
  dsimp only [conformalExperimentScale]
  nlinarith

lemma experiment_patch_subset_compact {s h : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hh : h ≤ s / 10) (w : ℂ) (hwn : ‖w‖ = 1) (hwy : s ≤ w.im) :
    closedBall w h ⊆ normalizedInteriorCompact s := by
  intro z hz
  have hn := norm_le_norm_add_const_of_dist_le hz
  have hi := Complex.im_le_norm (w - z)
  have hd : ‖w - z‖ ≤ h := by
    simpa only [mem_closedBall, ← dist_eq_norm, dist_comm] using hz
  rw [Complex.sub_im] at hi
  change ‖z‖ ≤ 2 ∧ s / 2 ≤ z.im
  rw [hwn] at hn
  constructor <;> linarith

lemma displaced_experiment_dist {h : ℝ} (hh : 0 ≤ h) (w z : ℂ)
    (hz : z ∈ closedBall (center h w) (h / 20)) :
    dist z w ≤ 3 * h / 10 := by
  have hd := (dist_triangle z (center h w) w).trans
    (add_le_add hz (center_dist hh w).le)
  linarith

lemma displaced_experiment_subset_patch {h : ℝ} (hh : 0 ≤ h) (w : ℂ) :
    closedBall (center h w) (h / 20) ⊆ closedBall w h := by
  intro z hz
  exact (displaced_experiment_dist hh w z hz).trans (by linarith)

lemma displaced_experiment_near_patch {h u : ℝ} (hh : 0 < h) (hu : u < h / 20)
    (w z y : ℂ) (hz : z ∈ closedBall (center h w) (h / 20)) (hzy : dist z y < u) :
    y ∈ closedBall w h := by
  have hd := dist_triangle y z w
  rw [dist_comm y z] at hd
  have hz' := displaced_experiment_dist hh.le w z hz
  change dist y w ≤ h
  linarith

/-- Converting any positive deterministic parameter cutoff into a
cutoff proportional to the physical conformal radius. -/
lemma conformal_experiment_mesh_cutoff {C a q v : ℝ}
    (hC : 0 < C) (ha : 0 < a) (hq : 0 < q) (w : ℂ) (hwi : w.im ≤ 1)
    (hv : v < (C * q / 2) * (2 * w.im * a)) :
    v / (C * a) < q := by
  apply (div_lt_iff₀ (mul_pos hC ha)).mpr
  have hm := mul_le_mul_of_nonneg_left hwi (show 0 ≤ C * q * a by positivity)
  nlinarith

theorem conformal_experiment_image_subset
    {s h c C : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hh : 0 < h)
    (hhs : h ≤ s / 10) (hCh : C * h ≤ s / 100) (hC : 0 < C)
    (F : ℂ → ℂ) (w : ℂ) (hwn : ‖w‖ = 1) (hwy : s ≤ w.im)
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hbound : ∀ z ∈ normalizedInteriorCompact s,
      c * ‖deriv F w‖ ≤ ‖deriv F z‖ ∧ ‖deriv F z‖ ≤ C * ‖deriv F w‖) :
    F '' closedBall (center h w) (h / 20) ⊆
      closedBall (F w) (2 * w.im * ‖deriv F w‖) := by
  let B : ℝ≥0 := ⟨C * ‖deriv F w‖, mul_nonneg hC.le (norm_nonneg _)⟩
  have hK := experiment_patch_subset_compact hs hs1 hhs w hwn hwy
  have hKH := hK.trans (normalizedInteriorCompact_subset_halfPlane hs)
  have hLip : LipschitzOnWith B F (closedBall w h) :=
    (convex_closedBall w h).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun z hz => ((hF.differentiableAt (isOpen_upperHalfPlane.mem_nhds (hKH hz))).hasDerivAt).hasDerivWithinAt)
      (fun z hz => by exact_mod_cast (hbound z (hK hz)).2)
  rintro _ ⟨z, hz, rfl⟩
  have hzK := displaced_experiment_subset_patch hh.le w hz
  have hd := hLip.dist_le_mul z hzK w (mem_closedBall_self hh.le)
  have hzdist := displaced_experiment_dist hh.le w z hz
  have hnonneg := norm_nonneg (deriv F w)
  have hmul := mul_le_mul_of_nonneg_right hCh hnonneg
  have hdist := mul_le_mul_of_nonneg_left hzdist (show 0 ≤ C * ‖deriv F w‖ by positivity)
  change dist (F z) (F w) ≤ 2 * w.im * ‖deriv F w‖
  change dist (F z) (F w) ≤ (C * ‖deriv F w‖) * dist z w at hd
  nlinarith

theorem conformal_experiment_restricted_transfer
    (κ : ℝ) {s h c C : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hh : 0 < h) (hhs : h ≤ s / 10) (hCh : C * h ≤ s / 100)
    (hc : 0 < c) (hC : 0 < C)
    (F : ℂ → ℂ) (w : ℂ) (hwn : ‖w‖ = 1) (hwy : s ≤ w.im)
    (hF : DifferentiableOn ℂ F upperHalfPlane) (hi : InjOn F upperHalfPlane)
    (hne : deriv F w ≠ 0)
    (hbound : ∀ z ∈ normalizedInteriorCompact s,
      c * ‖deriv F w‖ ≤ ‖deriv F z‖ ∧ ‖deriv F z‖ ≤ C * ‖deriv F w‖)
    (γ η : ℝ≥0 → ℂ) (a b : ℝ≥0)
    (heq : ∀ u ∈ Icc a b, γ u ∈ closedBall w h → η u = F (γ u))
    {v : ℝ} (hv : 0 < v)
    (hvc : v < (C * h / 40) * (2 * w.im * ‖deriv F w‖)) :
    ENNReal.ofReal ((c ^ 2 * (1 / C) ^ codimension κ) * ‖deriv F w‖ ^ dimension κ) *
        segmentSausageCharge κ γ a b (v / (C * ‖deriv F w‖))
          (closedBall (center h w) (h / 20)) ≤
      segmentSausageCharge κ η a b v (closedBall (F w) (2 * w.im * ‖deriv F w‖)) := by
  have hnorm : 0 < ‖deriv F w‖ := norm_pos_iff.mpr hne
  have hCa : 0 < C * ‖deriv F w‖ := mul_pos hC hnorm
  have hwi : w.im ≤ 1 := by simpa only [hwn] using Complex.im_le_norm w
  have hmesh : v / (C * ‖deriv F w‖) < h / 20 := by
    apply conformal_experiment_mesh_cutoff hC hnorm (by positivity) w hwi
    convert hvc using 1
    ring
  have hK := experiment_patch_subset_compact hs hs1 hhs w hwn hwy
  have hKH := hK.trans (normalizedInteriorCompact_subset_halfPlane hs)
  let B : ℝ≥0 := ⟨C * ‖deriv F w‖, hCa.le⟩
  have hstep : (1 / (C * ‖deriv F w‖)) * v = v / (C * ‖deriv F w‖) := by ring
  have ht := restricted_segment_sausage_conformal_transfer κ F (deriv F) γ η a b
    (closedBall (center h w) (h / 20)) (closedBall w h)
    (closedBall (F w) (2 * w.im * ‖deriv F w‖)) isClosed_closedBall.measurableSet
    (displaced_experiment_subset_patch hh.le w) (convex_closedBall w h)
    (hi.mono hKH)
    (fun z hz => (hF.differentiableAt (isOpen_upperHalfPlane.mem_nhds (hKH hz))).hasDerivAt)
    (mul_pos hc hnorm).le hv (one_div_pos.mpr hCa)
    (fun z hz => (hbound z (hK (displaced_experiment_subset_patch hh.le w hz))).1)
    B (fun z hz => by exact_mod_cast (hbound z (hK hz)).2)
    (by change (C * ‖deriv F w‖) * (1 / (C * ‖deriv F w‖)) ≤ 1; rw [mul_one_div_cancel hCa.ne'])
    (fun z hz y hd => displaced_experiment_near_patch hh hmesh w z y hz (by simpa only [hstep] using hd))
    heq (conformal_experiment_image_subset hs hs1 hh hhs hCh hC F w hwn hwy hF hbound)
  rw [conformal_transfer_coefficient κ hC hnorm, hstep] at ht
  exact ht

theorem uniform_conformal_experiment_restricted_transfer
    (κ : ℝ) (hcompact : PublishedHalfPlaneUnivalentCompactness)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ h A C δ : ℝ, 0 < h ∧ h ≤ s ∧ 0 < A ∧ 0 < C ∧ 0 < δ ∧
      ∀ (F : ℂ → ℂ) (w : ℂ), DifferentiableOn ℂ F upperHalfPlane →
        InjOn F upperHalfPlane → ‖w‖ = 1 → s ≤ w.im → deriv F w ≠ 0 →
        ∀ (γ η : ℝ≥0 → ℂ) (a b : ℝ≥0),
        (∀ u ∈ Icc a b, γ u ∈ closedBall w h → η u = F (γ u)) →
        ∀ v : ℝ, 0 < v → v < δ * (2 * w.im * ‖deriv F w‖) →
          ENNReal.ofReal (A * ‖deriv F w‖ ^ dimension κ) *
              segmentSausageCharge κ γ a b (v / (C * ‖deriv F w‖))
                (closedBall (center h w) (h / 20)) ≤
            segmentSausageCharge κ η a b v
              (closedBall (F w) (2 * w.im * ‖deriv F w‖)) := by
  obtain ⟨c, C, hc, hC, hbounds⟩ := uniform_waypoint_derivative_ratios hcompact hs hs1
  let h := conformalExperimentScale s C
  obtain ⟨hh, hhs, hCh⟩ := conformalExperimentScale_bounds hs hC
  refine ⟨h, c ^ 2 * (1 / C) ^ codimension κ, C, C * h / 40, hh,
    hhs.trans (by linarith), by positivity, hC, by positivity, ?_⟩
  intro F w hF hi hwn hwy hne γ η a b heq v hv hvc
  exact conformal_experiment_restricted_transfer κ hs hs1 hh hhs hCh hc hC
    F w hwn hwy hF hi hne (fun z hz => hbounds F w hF hi hwn hwy hne z hz.1 hz.2)
    γ η a b heq hv hvc

end SLEExactGauge.Serpentine

end

end OAI
