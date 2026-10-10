import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionStoppingScale

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)

def activeRegionLevel (t : ℕ) : Set (SupportCellDescendant μ R hR k z) :=
  {i | i.depth = t ∧ activeRegionCell Good i}

theorem activeRegionLevel_finite (t : ℕ) : (activeRegionLevel μ R hR k z Good t).Finite := by
  have hN := separated_set_finite_inter_compact (supportLatticeNets μ R hR (k + t)).points
    (closedBall (z : Ambient d) (2 * latticeRadius R k)) (latticeRadius R (k + t))
    (latticeRadius_pos R hR (k + t)) (supportLatticeNets μ R hR (k + t)).separated
    (isCompact_closedBall _ _)
  have himage : (SupportCellDescendant.center '' activeRegionLevel μ R hR k z Good t).Finite := by
    apply hN.subset
    rintro x ⟨i, hi, rfl⟩
    refine ⟨?_, i.center_dist_top⟩
    have hd : i.depth = t := hi.1
    rw [← hd]
    exact i.mem_net
  apply himage.of_finite_image
  intro i hi j hj hcenter
  apply i.eq_of_common_point_same_depth j (hi.1.trans hj.1.symm) i.center i.center_mem_cell
  rw [hcenter]
  exact j.center_mem_cell

theorem exists_active_level_center_of_small_stopping_scale (t : ℕ) (x : Ambient d)
    (hx : cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + t)) :
    ∃ i ∈ activeRegionLevel μ R hR k z Good t,
      dist x i.center < 3 * latticeRadius R (k + t) := by
  classical
  unfold cellRegionStoppingScale cappedStoppingDistance at hx
  obtain ⟨j, hj⟩ := exists_lt_of_ciInf_lt hx
  cases j with
  | none =>
    have hle := latticeRadius_antitone R hR.le (Nat.le_add_right k t)
    exact (not_lt_of_ge hle hj).elim
  | some j =>
    change dist x j.val.center + j.val.radius < latticeRadius R (k + t) at hj
    have hdepth : t ≤ j.val.depth := by
      by_contra h
      have hle := latticeRadius_antitone R hR.le (Nat.add_le_add_left (Nat.le_of_lt (Nat.lt_of_not_ge h)) k)
      change latticeRadius R (k + t) ≤ j.val.radius at hle
      have hd : 0 ≤ dist x j.val.center := dist_nonneg
      linarith
    obtain ⟨i, hi, hsub, hc⟩ := j.val.exists_ancestor_at_depth t hdepth
    have hactive := activeRegionCell_ancestor Good j.val i j.property (by omega) hsub
    have hrad : i.radius = latticeRadius R (k + t) := by simp only [SupportCellDescendant.radius, hi]
    have hcenter := i.dist_center_of_mem j.val.center hc
    have htri := dist_triangle x j.val.center i.center
    have hr := j.val.radius_pos
    refine ⟨i, ⟨hi, hactive⟩, ?_⟩
    rw [hrad] at hcenter
    linarith

theorem active_level_balls_cover_region_limit (t : ℕ) :
    cellRegionLimit μ R hR k z Good ⊆
      ⋃ i : activeRegionLevel μ R hR k z Good t,
        ball i.val.center (3 * latticeRadius R (k + t)) := by
  intro x hx
  have hsmall : cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + t) := by
    rw [cellRegionStoppingScale_eq_zero_of_region_limit μ R hR k z Good x hx]
    exact latticeRadius_pos R hR (k + t)
  obtain ⟨i, hi, hxi⟩ := exists_active_level_center_of_small_stopping_scale μ R hR k z Good t x hsmall
  exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩

end

end RieszRectifiability

end OAI
