import OAI.MeasureTheory.Falconer.Estimates.AllDimensions
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.HaarToSphere

namespace OAI

/-!
# The actual Euclidean sphere and its surface measure

The surface measure is induced by polar coordinates of Euclidean
Lebesgue measure.
-/

namespace Falconer
open Set MeasureTheory

abbrev Sphere (d : ℕ) := Metric.sphere (0 : Space d) 1

noncomputable def sphereMeasure (d : ℕ) : Measure (Sphere d) :=
  (volume : Measure (Space d)).toSphere

instance sphereMeasure_finite (d : ℕ) : IsFiniteMeasure (sphereMeasure d) := by
  unfold sphereMeasure
  infer_instance

@[simp] theorem sphere_norm {d : ℕ} (w : Sphere d) : ‖(w : Space d)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using w.property

end Falconer

end OAI
