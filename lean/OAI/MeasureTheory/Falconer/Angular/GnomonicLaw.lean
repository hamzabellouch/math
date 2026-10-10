import OAI.MeasureTheory.Falconer.Angular.GnomonicInverse

namespace OAI

/-! # Transporting an original direction law to its affine chart -/

namespace Falconer
open Set Metric MeasureTheory
variable {n : ℕ}

theorem gnomonicCoordinates_map_ball (ν : Measure (Sphere (n+1)))
    (hν : ∀ᵐ (w : Sphere (n+1)) ∂ν, 0 < (w:Space (n+1)) 0) (p : Space n) (r : ℝ) :
    (Measure.map gnomonicCoordinates ν) (ball p r) ≤ ν (ball (gnomonicChart p) (2*r)) := by
  rw [Measure.map_apply gnomonicCoordinates_measurable measurableSet_ball]
  apply measure_mono_ae
  filter_upwards [hν] with w hw hmem
  change dist (gnomonicCoordinates w) p < r at hmem
  change dist w (gnomonicChart p) < 2*r
  rw [← gnomonicChart_gnomonicCoordinates w hw]
  exact (gnomonicChart_distance_le (gnomonicCoordinates w) p).trans_lt (by linarith)

theorem gnomonicCoordinates_map_recover (ν : Measure (Sphere (n+1)))
    (hν : ∀ᵐ (w : Sphere (n+1)) ∂ν, 0 < (w:Space (n+1)) 0) :
    Measure.map gnomonicChart (Measure.map gnomonicCoordinates ν) = ν := by
  rw [Measure.map_map (gnomonicChart_continuous n).measurable gnomonicCoordinates_measurable]
  calc
    _ = Measure.map id ν := Measure.map_congr (by
      filter_upwards [hν] with w hw
      exact gnomonicChart_gnomonicCoordinates w hw)
    _ = ν := Measure.map_id

end Falconer

end OAI
