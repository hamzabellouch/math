import OAI.GroupTheory.PolycyclicRecognition.Analysis.StationarySlope
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace OAI

/-! # Distance to a finite label set from one L2 approximation

The comparison uses any one label known on the fixed component. Its
conclusion takes distance to the whole set and needs no selection of labels.
-/

namespace PolycyclicRecognition

open MeasureTheory Metric
open scoped ENNReal

variable {X W : Type*} [MeasurableSpace X] [NormedAddCommGroup W]

/-- An L2 approximation to one point of a set bounds the average distance
to the whole set on a probability space. -/
theorem lintegral_infDist_le_L2 (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → W) (v : Lp W 2 μ) {S : Set W} {w : W} (hw : w ∈ S)
    (hv : (v : X → W) =ᵐ[μ] fun x => f x - w) :
    ∫⁻ x, ENNReal.ofReal (infDist (f x) S) ∂μ ≤ ENNReal.ofReal ‖v‖ := by
  calc
    _ ≤ ∫⁻ x, ‖v x‖ₑ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hv] with x hx
      rw [← ofReal_norm, hx]
      apply ENNReal.ofReal_le_ofReal
      simpa only [dist_eq_norm] using infDist_le_dist_of_mem hw
    _ = eLpNorm v 1 μ := (eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable v)).symm
    _ ≤ eLpNorm v 2 μ := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
    _ = ENNReal.ofReal ‖v‖ := by rw [ofReal_norm, Lp.enorm_def]

end PolycyclicRecognition

end OAI
