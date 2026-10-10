import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! # Turning a power-small incidence into a power-small direction mass -/

namespace Falconer
open scoped ENNReal

theorem ennreal_mass_of_power_incidence {δ b c : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hbc : 2*b ≤ c) (M : ℝ≥0∞)
    (h : ENNReal.ofReal (δ^b)*M ≤ ENNReal.ofReal (δ^c)) : M ≤ ENNReal.ofReal (δ^b) := by
  have h0 : ENNReal.ofReal (δ^b) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ _))
  have hh := mul_le_mul' (le_refl ((ENNReal.ofReal (δ^b))⁻¹)) h
  rw [← mul_assoc,ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top,one_mul] at hh
  apply hh.trans
  rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hδ _),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.rpow_neg hδ.le,← Real.rpow_add hδ]
  exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)

end Falconer

end OAI
