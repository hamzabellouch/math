import OAI.Analysis.CircleDomains.Topology.HalfPlaneRay
import OAI.Analysis.CircleDomains.Reflection.CayleyBoundaryOrder
import OAI.Analysis.CircleDomains.Topology.DiskBoundarySide

namespace OAI

/-! Side functions for all integer translates of a lifted ray. Boundary
order is the ordinary order on the real boundary of the half-plane. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

namespace HalfPlaneRay

def IsJordan (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ) : Prop :=
  frontier (jordanInterior H) = range R.crosscut ∪ range (boundaryClosingArc _ R.crosscut_start_norm)

theorem exists_jordan (R : HalfPlaneRay) (hsch : PlanarSchoenflies) :
    ∃ H : ℂ ≃ₜ ℂ, R.IsJordan H := by
  obtain ⟨H, hH⟩ := R.exists_schoenflies hsch
  refine ⟨H, ?_⟩
  unfold IsJordan
  rw [frontier_jordanInterior_eq_circle_range H _ hH]
  have hr := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.surjective.range_comp
    (circleOfClosedPath (R.crosscut.trans (boundaryClosingArc _ R.crosscut_start_norm)))
  rw [show (fun z : Circle => circleOfClosedPath (R.crosscut.trans
      (boundaryClosingArc _ R.crosscut_start_norm))
      ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z)) =
      (circleOfClosedPath (R.crosscut.trans (boundaryClosingArc _ R.crosscut_start_norm))) ∘
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm from rfl,
    hr, circleOfClosedPath_range, Path.trans_range]

theorem crosscut_norm_le (R : HalfPlaneRay) (t : PathTime) : ‖R.crosscut t‖ ≤ 1 := by
  by_cases ht : t < ⊤
  · change ‖R.compactify t‖ ≤ 1
    rw [compactify, dite_eq_left ht]
    exact halfPlaneDisk_norm_le (R.nonneg _)
  · have he : t = ⊤ := top_le_iff.mp (not_lt.mp ht)
    subst t
    change ‖R.compactify ⊤‖ ≤ 1
    rw [R.compactify_top, norm_one]

theorem filling_subset (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) :
    closure (jordanInterior H) ⊆ Metric.closedBall 0 1 ∧
      jordanInterior H ⊆ Metric.ball 0 1 := by
  have hcl : closure (jordanInterior H) ⊆ Metric.closedBall 0 1 := by
    apply jordan_fill_subset_closed_unitDisk
    intro z hz
    rw [hH] at hz
    rcases hz with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact R.crosscut_norm_le t
    · exact (boundaryClosingArc_norm _ _ t).le
  refine ⟨hcl, ?_⟩
  have hi := interior_mono hcl
  rwa [interior_closure_jordanInterior, interior_closedBall _ one_ne_zero] at hi

abbrev CutDomain (R : HalfPlaneRay) := {z : ℂ // z ∈ Metric.closedBall 0 1 \ range R.crosscut}

def side (R : HalfPlaneRay) (H : ℂ ≃ₜ ℂ) (z : R.CutDomain) : Bool :=
  if z.val ∈ closure (jordanInterior H) then false else true

theorem isLocallyConstant_side (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H) :
    IsLocallyConstant (R.side H) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro z
  by_cases hz : z.val ∈ closure (jordanInterior H)
  · have hn : ∃ ε > 0, Metric.ball z.val ε ∩ Metric.closedBall 0 1 ⊆
        closure (jordanInterior H) := by
      by_cases hi : z.val ∈ jordanInterior H
      · obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.mp (jordanInterior_isOpen H) z.val hi
        exact ⟨ε, hε, fun _ h => subset_closure (hB h.1)⟩
      · have hf : z.val ∈ frontier (jordanInterior H) := by
          rw [(jordanInterior_isOpen H).frontier_eq]
          exact ⟨hz, hi⟩
        obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.mp
          (isCompact_range R.crosscut.continuous).isClosed.isOpen_compl z.val z.property.2
        refine ⟨ε, hε, closed_disk_neighborhood_in_filling H (R.filling_subset hH).2 hf hε ?_⟩
        rintro w ⟨hw, hwf⟩
        rw [hH] at hwf
        rcases hwf with hwc | ⟨t, rfl⟩
        · exact (hB hw hwc).elim
        · exact mem_sphere_zero_iff_norm.mpr (boundaryClosingArc_norm _ _ t)
    obtain ⟨ε, hε, hB⟩ := hn
    have hnear : ∀ᶠ w : R.CutDomain in 𝓝 z, w.val ∈ Metric.ball z.val ε :=
      continuous_subtype_val.continuousAt.eventually
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
    filter_upwards [hnear] with w hw
    simp only [side, ite_eq_left hz, ite_eq_left (hB ⟨hw, w.property.1⟩)]
  · have hnear : ∀ᶠ w : R.CutDomain in 𝓝 z, w.val ∈ (closure (jordanInterior H))ᶜ :=
      continuous_subtype_val.continuousAt.eventually (isClosed_closure.isOpen_compl.mem_nhds hz)
    filter_upwards [hnear] with w hw
    simp only [side, ite_eq_right hz, ite_eq_right hw]

theorem start_eq_real (R : HalfPlaneRay) :
    R.compactify 0 = halfPlaneDisk ((R.curve ⟨0, bot_lt_top⟩).re : ℂ) := by
  have ht : (0 : PathTime) < ⊤ := bot_lt_top
  rw [compactify, dite_eq_left ht]
  congr 1
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using R.start

theorem side_boundary (R : HalfPlaneRay) {H : ℂ ≃ₜ ℂ} (hH : R.IsJordan H)
    (x : ℝ) (hmiss : halfPlaneDisk x ∉ range R.crosscut) :
    R.side H ⟨halfPlaneDisk x, Metric.mem_closedBall.mpr
      (by simpa only [dist_zero_right] using (cayleyBoundary_norm x).le), hmiss⟩ =
      if x ≤ (R.curve ⟨0, bot_lt_top⟩).re then false else true := by
  have hnot : halfPlaneDisk x ∉ jordanInterior H := by
    intro hi
    have hl : ‖halfPlaneDisk x‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using (R.filling_subset hH).2 hi
    rw [cayleyBoundary_norm] at hl
    exact lt_irrefl _ hl
  have hc : halfPlaneDisk x ∈ closure (jordanInterior H) ↔ x ≤ (R.curve ⟨0, bot_lt_top⟩).re := by
    have he : halfPlaneDisk x ∈ closure (jordanInterior H) ↔ halfPlaneDisk x ∈ frontier (jordanInterior H) := by
      rw [(jordanInterior_isOpen H).frontier_eq]
      simp only [Set.mem_sdiff, hnot, not_false_eq_true, and_true]
    rw [he, hH, mem_union, or_iff_right hmiss]
    have hb := cayleyBoundary_mem_closingArc (R.curve ⟨0, bot_lt_top⟩).re x
    have heq : (fun t : PathTime => boundaryClosingArc (R.compactify 0) R.crosscut_start_norm t) =
        (fun t : PathTime => boundaryClosingArc
          (halfPlaneDisk ((R.curve ⟨0, bot_lt_top⟩).re : ℂ))
          (cayleyBoundary_norm (R.curve ⟨0, bot_lt_top⟩).re) t) := by
      funext t
      change standardCirclePoint _ = standardCirclePoint _
      rw [R.start_eq_real]
    change halfPlaneDisk x ∈ range (fun t : PathTime =>
      boundaryClosingArc (R.compactify 0) R.crosscut_start_norm t) ↔ _
    rw [heq]
    exact hb
  simp only [side, hc]

end HalfPlaneRay
end CircleDomainRigidity

end

end OAI
