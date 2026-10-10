import OAI.MeasureTheory.Falconer.Radial.AffineSlabCluster
import OAI.MeasureTheory.Falconer.Angular.AngularTubes

namespace OAI

/-! # Separation of unoriented normals controls their transverse component -/

namespace Falconer
variable {d : ℕ}

theorem normalDistance_le_perpendicular {u v : Space d}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    normalDistance u v ≤ 2*‖perpendicularPart u v‖ := by
  by_cases h : 0 ≤ inner ℝ u v
  · exact (min_le_left _ _).trans (unit_close_of_perpendicular hu hv h)
  · have hneg : 0 ≤ inner ℝ u (-v) := by
      rw [inner_neg_right]
      linarith only [h]
    have hn : ‖-v‖ = 1 := by simpa only [norm_neg] using hv
    have hh := unit_close_of_perpendicular hu hn hneg
    have he : perpendicularPart u (-v) = -(perpendicularPart u v) := by
      simp only [perpendicularPart,inner_neg_right,neg_smul]
      abel
    rw [he,norm_neg,sub_neg_eq_add] at hh
    exact (min_le_right _ _).trans hh

end Falconer

end OAI
