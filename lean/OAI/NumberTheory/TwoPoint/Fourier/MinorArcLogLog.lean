import OAI.NumberTheory.TwoPoint.Fourier.MinorArcTypicalSaving

namespace OAI

/-! The dyadic index count contributes only a logarithm of a logarithm. -/

namespace TwoPointCorrelations

lemma minor_arc_log_index_bound (H : ℕ) (hH : 1 ≤ H) :
    (Nat.log 2 H : ℝ) ≤ 2 * Real.log (H : ℝ) := by
  have hH0 : H ≠ 0 := by omega
  have hp : (2 : ℝ) ^ Nat.log 2 H ≤ H := by
    exact_mod_cast Nat.pow_log_le_self 2 hH0
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 H) hp
  rw [Real.log_pow] at hl
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hm := mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg (Nat.log 2 H) :
    (0 : ℝ) ≤ Nat.log 2 H)
  nlinarith

lemma minor_arc_dyadic_log_log_bound (H : ℕ) (hH : 2 ≤ H)
    (hlogH : 1 ≤ Real.log (H : ℝ)) (hloglogH : 1 ≤ Real.log (Real.log (H : ℝ))) :
    1 + Real.log (Nat.log 2 H : ℝ) ≤ 3 * Real.log (Real.log (H : ℝ)) := by
  have hindex : 0 < Nat.log 2 H := lt_of_lt_of_le (by norm_num)
    (minor_arc_dyadic_index_pos hH)
  have hindex0 : (0 : ℝ) < Nat.log 2 H := by exact_mod_cast hindex
  have hlog0 : 0 < Real.log (H : ℝ) := by linarith
  have hh := Real.log_le_log hindex0 (minor_arc_log_index_bound H (by omega))
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlog0.ne'] at hh
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

end TwoPointCorrelations

end OAI
