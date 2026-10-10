import OAI.Probability.SLE.Gauge.WaypointBrownianPassages
import OAI.Probability.SLE.Geometry.FirstDomainExit

namespace OAI

/-! The two actual physical waypoint tubes start on opposite local sides
of any correctly straightened access guide.  The local side assertion is
derived from openness; it is not a ribbon-angle input. -/

noncomputable section
open Set Metric MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.RibbonCoordinates
open CrosscutSides

theorem waypoint_quarter_ball_side
    (k side : ℝ) (hside : side = -1 ∨ side = 1) {z : ℂ}
    (hz : z ∈ ball (waypointRoute k side (1 / 4)) (1 / 32)) :
    z ∈ ball ((k + 1 / 2 : ℝ) : ℂ) (1 / 4) ∧ 0 < side * z.im := by
  have habs : |side| = 1 := by rcases hside with rfl | rfl <;> norm_num
  have he : waypointRoute k side (1 / 4) =
      ((k + 1 / 2 : ℝ) : ℂ) + ((side / 8 : ℝ) : ℂ) * Complex.I := by
    simp only [waypointRoute, unitClip]
    norm_num
    congr 1
    ring
  have hdist : dist (waypointRoute k side (1 / 4)) ((k + 1 / 2 : ℝ) : ℂ) = 1 / 8 := by
    rw [he, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div, habs]
    norm_num
  have him := (Complex.abs_im_le_norm (z - waypointRoute k side (1 / 4))).trans_lt
    (show ‖z - waypointRoute k side (1 / 4)‖ < 1 / 32 by
      simpa only [mem_ball, dist_eq_norm] using hz)
  rw [Complex.sub_im, he, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re] at him
  norm_num at him
  constructor
  · have hh := dist_triangle z (waypointRoute k side (1 / 4)) ((k + 1 / 2 : ℝ) : ℂ)
    rw [hdist] at hh
    have hz' : dist z (waypointRoute k side (1 / 4)) < 1 / 32 := hz
    exact lt_of_le_of_lt hh (by linarith)
  · have hh := abs_lt.mp him
    rcases hside with rfl | rfl <;> norm_num at * <;> linarith

theorem physical_quarter_tube_coordinate
    (hopen : PublishedPlanarDiskOpenness)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hi : InjOn P closedRibbon)
    (K : ℝ≥0) (hK : 0 < (K : ℝ)) {k side : ℝ}
    (hk : 1 ≤ k) (hside : side = -1 ∨ side = 1)
    (hlower : ∀ v ∈ crossingPatch k, ∀ w ∈ crossingPatch k,
      dist v w ≤ K * dist (P v) (P w)) {y : ℂ}
    (hy : dist y (P (waypointRoute k side (1 / 4))) < (1 / 32 : ℝ) / K) :
    ∃ z ∈ ball ((k + 1 / 2 : ℝ) : ℂ) (1 / 4), 0 < side * z.im ∧ P z = y := by
  have habs : |side| = 1 := by rcases hside with rfl | rfl <;> norm_num
  have hpatch := waypointRoute_ball_subset_patch k side habs (1 / 4)
  have hsub := crossingPatch_subset_closedRibbon hk
  have hball := ball_subset_closedBall.trans (hpatch.trans hsub)
  obtain ⟨z, hz, he⟩ := ball_subset_image_ball P (waypointRoute k side (1 / 4))
    (by norm_num : (0 : ℝ) < 1 / 32) hK (hP.mono (hpatch.trans hsub))
    (hopen P _ _ (by norm_num) (hP.mono hball) (hi.mono hball))
    (fun z hz => hlower z (hpatch hz) _ (hpatch (mem_closedBall_self (by norm_num)))) hy
  exact ⟨z, (waypoint_quarter_ball_side k side hside hz).1,
    (waypoint_quarter_ball_side k side hside hz).2, he⟩

/-- Any local straightening of the access guide fixes one orientation for
the entire pair of physical quarter-time tube neighborhoods. -/
theorem physical_waypoint_tubes_opposite_sides
    (hopen : PublishedPlanarDiskOpenness)
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hi : InjOn P closedRibbon)
    (K : ℝ≥0) (hK : 0 < (K : ℝ)) {k : ℝ} (hk : 1 ≤ k)
    (hlower : ∀ v ∈ crossingPatch k, ∀ w ∈ crossingPatch k,
      dist v w ≤ K * dist (P v) (P w))
    (f : ℂ → ℂ) (j : ℂ → ℝ)
    (hf : ContinuousOn f (ball ((k + 1 / 2 : ℝ) : ℂ) (1 / 4)))
    (hfi : InjOn f (ball ((k + 1 / 2 : ℝ) : ℂ) (1 / 4)))
    (hzero : ∀ z ∈ ball ((k + 1 / 2 : ℝ) : ℂ) (1 / 4),
      (f z).re = 0 ↔ z.im = 0)
    (hrel : ∀ z ∈ ball ((k + 1 / 2 : ℝ) : ℂ) (1 / 4), j (P z) = (f z).re) :
    ∃ side : ℝ, (side = -1 ∨ side = 1) ∧
      (∀ y : ℂ, dist y (P (waypointRoute k side (1 / 4))) < (1 / 32 : ℝ) / K →
        0 < j y) ∧
      (∀ y : ℂ, dist y (P (waypointRoute k (-side) (1 / 4))) < (1 / 32 : ℝ) / K →
        j y < 0) := by
  have hcenter : (f ((k + 1 / 2 : ℝ) : ℂ)).re = 0 :=
    (hzero _ (mem_ball_self (by norm_num))).mpr (by simp)
  have hsides := opposite_half_disk_signs f ((k + 1 / 2 : ℝ) : ℂ)
    (by norm_num) hf (hopen f _ _ (by norm_num) hf hfi) hcenter hzero
  rcases hsides with ⟨hpos, hneg⟩ | ⟨hneg, hpos⟩
  · refine ⟨1, Or.inr rfl, ?_, ?_⟩
    · intro y hy
      obtain ⟨z, hz, hi', rfl⟩ := physical_quarter_tube_coordinate hopen P hP hi K hK
        hk (Or.inr rfl) hlower hy
      rw [hrel z hz]
      exact hpos z hz (by simpa using hi')
    · intro y hy
      obtain ⟨z, hz, hi', rfl⟩ := physical_quarter_tube_coordinate hopen P hP hi K hK
        hk (Or.inl rfl) hlower hy
      rw [hrel z hz]
      exact hneg z hz (by nlinarith)
  · refine ⟨-1, Or.inl rfl, ?_, ?_⟩
    · intro y hy
      obtain ⟨z, hz, hi', rfl⟩ := physical_quarter_tube_coordinate hopen P hP hi K hK
        hk (Or.inl rfl) hlower hy
      rw [hrel z hz]
      exact hpos z hz (by nlinarith)
    · intro y hy
      have hy' : dist y (P (waypointRoute k 1 (1 / 4))) < (1 / 32 : ℝ) / K := by
        simpa only [neg_neg] using hy
      obtain ⟨z, hz, hi', rfl⟩ := physical_quarter_tube_coordinate hopen P hP hi K hK
        hk (Or.inr rfl) hlower hy'
      rw [hrel z hz]
      exact hneg z hz (by simpa using hi')

end SLEExactGauge.RibbonCoordinates

end

end OAI
