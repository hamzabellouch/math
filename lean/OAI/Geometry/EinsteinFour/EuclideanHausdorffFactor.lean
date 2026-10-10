import OAI.Geometry.EinsteinFour.RiemannianVolume
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace OAI

/-! The Euclidean four-dimensional Hausdorff measure is a fixed positive
multiple of Lebesgue measure. Its numerical normalization is immaterial
for the normalized canonical frame measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped ENNReal NNReal

noncomputable section

local instance : Measure.IsAddHaarMeasure
    (Measure.hausdorffMeasure 4 : Measure FourSpace) := by
  simpa [FourSpace] using
    (inferInstance : Measure.IsAddHaarMeasure
      (Measure.hausdorffMeasure (Module.finrank ℝ FourSpace) : Measure FourSpace))

def euclideanHausdorffFactor : ℝ≥0 :=
  (Measure.hausdorffMeasure 4 : Measure FourSpace).addHaarScalarFactor volume

theorem euclideanHausdorffFactor_pos : 0 < euclideanHausdorffFactor :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem euclideanHausdorff_eq_smul_volume :
    (Measure.hausdorffMeasure 4 : Measure FourSpace) = euclideanHausdorffFactor • volume :=
  Measure.isAddLeftInvariant_eq_smul _ _

theorem euclideanHausdorff_apply (s : Set FourSpace) :
    (Measure.hausdorffMeasure 4 : Measure FourSpace) s =
      (euclideanHausdorffFactor : ℝ≥0∞) * volume s := by
  rw [euclideanHausdorff_eq_smul_volume, Measure.smul_apply]
  rfl

end
end PositiveEinsteinFour.Geometry

end OAI
