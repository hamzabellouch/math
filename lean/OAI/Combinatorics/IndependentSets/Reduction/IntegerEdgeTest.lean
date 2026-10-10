import Mathlib

namespace OAI

namespace LargeIndependentSets.ShortestPaths
open scoped ENNReal

lemma integer_edge_test {D : ℕ} [NeZero D] (c : ℕ∞) :
    (c:ℝ≥0∞)/(D:ℝ≥0∞) ≤ ENNReal.ofReal (1/8) ↔ 8*c ≤ (D:ℕ∞) := by
  induction c using ENat.recTopCoe with
  | top => simp [ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top D)]
  | coe c =>
    have hd : 0 < (D:ℝ) := by exact_mod_cast (NeZero.pos D)
    have hD : (D:ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.ne D)
    rw [← ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by simp) hD) (by simp)]
    simp only [ENat.toENNReal_coe,ENNReal.toReal_div,ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/8)]
    rw [div_le_iff₀ hd]
    have hr : (c:ℝ) ≤ 1/8*(D:ℝ) ↔ 8*(c:ℝ) ≤ (D:ℝ) := by constructor <;> intro h <;> linarith
    rw [hr]
    have he : (8:ℕ∞)*(c:ℕ∞) = ((8*c:ℕ):ℕ∞) := by norm_cast
    rw [he,ENat.natCast_le_natCast]
    exact_mod_cast Iff.rfl

end LargeIndependentSets.ShortestPaths

end OAI
