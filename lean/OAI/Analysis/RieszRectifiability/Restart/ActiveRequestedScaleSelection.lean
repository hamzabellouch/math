import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveSuccessorFiveBall
import OAI.Analysis.RieszRectifiability.Nets.LatticeRadiusAbove

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_active_cell_at_requested_radius {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (p : Ambient d) (r : ℝ) (hr : 0 < r) (hrtop : r ≤ latticeRadius R k / 16)
    (hD : cellRegionStoppingScale μ R hR k z Good p < r / 4) :
    ∃ t : ℕ, ∃ q ∈ activeLevelIndex μ R hR k z Good t,
      16 * r ≤ q.radius ∧ q.radius ≤ 1024 * r ∧
      dist p q.center < (131 / 64 : ℝ) * q.radius := by
  obtain ⟨t, htlo, hthi⟩ := exists_lattice_radius_above R k (16 * r) (by positivity) (by linarith)
  have hDlevel : cellRegionStoppingScale μ R hR k z Good p < latticeRadius R (k + (t + 1)) := by
    rw [← Nat.add_assoc, latticeRadius_succ]
    linarith
  obtain ⟨i, hi, hpi⟩ := exists_active_level_center_of_small_stopping_scale
    μ R hR k z Good (t + 1) p hDlevel
  have hiF : i ∈ activeLevelIndex μ R hR k z Good (t + 1) :=
    (mem_activeLevelIndex μ R hR k z Good (t + 1) i).mpr hi
  obtain ⟨q, hq, hscale, hcenters, _⟩ :=
    active_successor_parent_captures_five_ball μ R hR k z Good t i hiF
  have hqdepth := ((mem_activeLevelIndex μ R hR k z Good t q).mp hq).1
  have hqr : q.radius = latticeRadius R (k + t) := by
    simp only [SupportCellDescendant.radius, hqdepth]
  have hir : i.radius = latticeRadius R (k + (t + 1)) := by
    simp only [SupportCellDescendant.radius, hi.1]
  rw [← hir] at hpi
  refine ⟨t, q, hq, ?_, ?_, ?_⟩
  · rwa [hqr]
  · rw [hqr]
    linarith
  · have ht := dist_triangle p i.center q.center
    nlinarith

end

end RieszRectifiability

end OAI
