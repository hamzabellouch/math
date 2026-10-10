import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.SurfaceBallCellCover

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem surface_ball_cell_mass_sum_le {n d : ℕ}
    (ν : Measure (Ambient d)) (G : ℝ) (hg : GlobalUpperGrowth n G ν)
    (r : ℝ) (hr : 0 < r) (a : Ambient d) :
    (∑ z : surfaceBallCellCenters ν r hr a, ν (cleanSupportCell ν r hr 0 z.val)) ≤
      ENNReal.ofReal (G * (8 * r) ^ n) := by
  let F := surfaceBallCellCenters ν r hr a
  have hd : Pairwise (fun z w : F => Disjoint (cleanSupportCell ν r hr 0 z.val)
      (cleanSupportCell ν r hr 0 w.val)) := by
    intro z w hzw
    exact cleanSupportCell_disjoint ν r hr 0 z.val w.val (fun h => hzw (Subtype.ext h))
  have hm : ∀ z : F, MeasurableSet (cleanSupportCell ν r hr 0 z.val) :=
    fun z => cleanSupportCell_measurable ν r hr 0 z.val
  have hsum : (∑ z : F, ν (cleanSupportCell ν r hr 0 z.val)) =
      ν (⋃ z : F, cleanSupportCell ν r hr 0 z.val) := by
    simpa only [tsum_fintype] using! (measure_iUnion hd hm).symm
  have hsub : (⋃ z : F, cleanSupportCell ν r hr 0 z.val) ⊆ ball a (8 * r) := by
    apply iUnion_subset
    intro z
    exact (selected_surface_ball_cell_subset_seven_ball ν r hr a z.val z.property).trans
      (closedBall_subset_ball (by linarith : 7 * r < 8 * r))
  rw [hsum]
  exact (measure_mono hsub).trans (hg.2 a _ (by positivity))

end

end RieszRectifiability

end OAI
