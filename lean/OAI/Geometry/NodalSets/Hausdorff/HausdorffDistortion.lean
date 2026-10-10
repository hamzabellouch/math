import Mathlib.MeasureTheory.Measure.Hausdorff

namespace OAI

namespace Yau.Geometry
open scoped ENNReal NNReal

lemma ofReal_le_of_fourth_power_mul_le {A : ℝ} {C : ℝ≥0} (hC : 0 < C)
    {m : ℝ≥0∞} (h : ENNReal.ofReal A ≤ (C : ℝ≥0∞)^4*m) :
    ENNReal.ofReal (A/(C:ℝ)^4) ≤ m := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.div_le_iff' (by positivity) (by finiteness)).mpr h

end Yau.Geometry

end OAI
