import OAI.Probability.SLE.Geometry.WaypointRoutes

namespace OAI

/-! After the initial free move, either waypoint route remains a fixed
distance from the complete access guide. Embedded coordinate disks turn
this into physical separation, including nonlocal pieces of the guide. -/

noncomputable section
open Set Metric
open scoped Topology NNReal

namespace SLEExactGauge.RibbonCoordinates

theorem waypointRoute_before_two_offset
    (k side : ℝ) (hside : |side| = 1) {t : ℝ}
    (ht : t ∈ Icc (1 / 4 : ℝ) 2) :
    1 / 8 ≤ |(waypointRoute k side t).im| := by
  have hclip : 1 / 4 ≤ unitClip t :=
    (show 1 / 4 ≤ min 1 t from le_min (by norm_num) ht.1).trans (le_max_right _ _)
  rw [waypointRoute_im, unitClip_of_nonpos (by linarith [ht.2] : t - 2 ≤ 0),
    sub_zero, abs_mul, hside, one_mul, abs_of_nonneg (by positivity)]
  linarith

theorem waypointRoute_guide_separation
    (k side : ℝ) (hside : |side| = 1) {x t u : ℝ}
    (hx : |x| ≤ 1 / 16) (ht : 1 / 4 ≤ t) (hu : 0 ≤ u) :
    1 / 16 ≤ dist (waypointRoute k side t) (guideCoordinate k x u) := by
  by_cases ht2 : t ≤ 2
  · have hroute := waypointRoute_before_two_offset k side hside ⟨ht, ht2⟩
    have hguide := (guideCoordinate_im_bound (k := k) (x := x) hu).trans hx
    have hh : |(waypointRoute k side t).im| ≤
        |(waypointRoute k side t).im - (guideCoordinate k x u).im| +
          |(guideCoordinate k x u).im| := by
      simpa only [sub_add_cancel] using abs_add_le
        ((waypointRoute k side t).im - (guideCoordinate k x u).im)
        (guideCoordinate k x u).im
    have hn := Complex.abs_im_le_norm (waypointRoute k side t - guideCoordinate k x u)
    rw [Complex.sub_im] at hn
    rw [dist_eq_norm]
    linarith
  · have hc : unitClip (t - 1) = 1 := unitClip_of_one_le (by linarith)
    have hn := Complex.abs_re_le_norm (waypointRoute k side t - guideCoordinate k x u)
    rw [Complex.sub_re, waypointRoute_re, guideCoordinate_re, hc] at hn
    have hh := neg_le_abs (k + 1 / 2 - 1 - (k + u))
    rw [dist_eq_norm]
    linarith

theorem waypointRoute_ball_subset_patch
    (k side : ℝ) (hside : |side| = 1) (t : ℝ) :
    closedBall (waypointRoute k side t) (1 / 32) ⊆ crossingPatch k := by
  intro z hz
  have hn : ‖z - waypointRoute k side t‖ ≤ 1 / 32 := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have hre := (Complex.abs_re_le_norm (z - waypointRoute k side t)).trans hn
  have him := (Complex.abs_im_le_norm (z - waypointRoute k side t)).trans hn
  rw [Complex.sub_re, waypointRoute_re] at hre
  rw [Complex.sub_im] at him
  have hclip0 := unitClip_nonneg (t - 1)
  have hclip1 := unitClip_le_one (t - 1)
  have hr := abs_le.mp hre
  have hi := abs_le.mp him
  have hri := abs_le.mp (waypointRoute_im_bound k side hside t)
  exact ⟨by linarith, by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- Physical separation follows from the full ribbon embedding: a nonlocal
guide point cannot enter the image of a local coordinate disk either. -/
theorem physical_waypointRoute_avoids_complete_guide
    (hpublished : PublishedPlanarDiskOpenness)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hi : InjOn P closedRibbon)
    (K : ℝ≥0) (hK : 0 < (K : ℝ)) {k x side t u : ℝ}
    (hk : 1 ≤ k) (hx : |x| ≤ 1 / 16) (hside : |side| = 1)
    (hlower : ∀ v ∈ crossingPatch k, ∀ w ∈ crossingPatch k,
      dist v w ≤ K * dist (P v) (P w))
    (ht : 1 / 4 ≤ t) (hu : 0 ≤ u) :
    P (guideCoordinate k x u) ∉ ball (P (waypointRoute k side t)) ((1 / 32 : ℝ) / K) := by
  intro hmem
  have hpatch := waypointRoute_ball_subset_patch k side hside t
  have hsub := crossingPatch_subset_closedRibbon hk
  have hball : ball (waypointRoute k side t) (1 / 32) ⊆ closedRibbon :=
    ball_subset_closedBall.trans (hpatch.trans hsub)
  obtain ⟨z, hz, he⟩ := ball_subset_image_ball P (waypointRoute k side t)
    (by norm_num : (0 : ℝ) < 1 / 32) hK (hP.mono (hpatch.trans hsub))
    (hpublished P _ _ (by norm_num) (hP.mono hball) (hi.mono hball))
    (fun z hz => hlower z (hpatch hz) _ (hpatch (mem_closedBall_self (by norm_num)))) hmem
  have hguide : guideCoordinate k x u ∈ closedRibbon :=
    ⟨by rw [guideCoordinate_re]; linarith,
      (guideCoordinate_im_bound hu).trans (hx.trans (by norm_num))⟩
  have heq : z = guideCoordinate k x u := hi (hball hz) hguide he
  have hd := waypointRoute_guide_separation k side hside hx ht hu
  rw [heq, mem_ball, dist_comm] at hz
  linarith

end SLEExactGauge.RibbonCoordinates

end

end OAI
