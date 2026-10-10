import OAI.Analysis.LipschitzHilbert.Estimates.BoxPolynomialWeight
import OAI.Analysis.LipschitzHilbert.Estimates.PolynomialEnvelope

namespace OAI

/-! Transverse decay of the reference-line envelope for centers in an
actual offset box. -/

noncomputable section

namespace LipschitzHilbert

theorem transverse_box_envelope (s y W b : ℝ) (n : ℕ) (hW : 0 < W)
    (hbox : |s - (y + W * b)| ≤ W) :
    lineEnvelope s W n y ≤ (((1 + |b|) ^ 2 / 8) ^ n)⁻¹ := by
  have hx : |(2 * y + W * b - s) - y| ≤ W := by
    have heq : (2 * y + W * b - s) - y = -(s - (y + W * b)) := by ring
    rw [heq, abs_neg]
    exact hbox
  have hb := box_polynomial_base y W b (2 * y + W * b - s) hW hx
  have heq : (2 * y + W * b - s) - (y + W * b) = y - s := by ring
  rw [heq, ← div_pow] at hb
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + |b|) ^ 2 / 8) hb n
  exact inv_anti₀ (by positivity) hp

theorem box_decay_le_line_envelope (b : ℝ) :
    (((1 + |b|) ^ 2 / 8) ^ 2)⁻¹ ≤ 64 * lineEnvelope 0 1 1 b ^ 2 := by
  have hbase : 1 + b ^ 2 ≤ (1 + |b|) ^ 2 := by nlinarith [abs_nonneg b, sq_abs b]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + b ^ 2) hbase 2
  have hinv := inv_anti₀ (by positivity : 0 < (1 + b ^ 2) ^ 2) hp
  have heq : (((1 + |b|) ^ 2 / 8) ^ 2)⁻¹ = 64 * (((1 + |b|) ^ 2) ^ 2)⁻¹ := by
    rw [div_pow, inv_div]
    norm_num
    ring
  rw [heq]
  have h := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 64)
  simpa only [lineEnvelope, sub_zero, div_one, pow_one, inv_pow] using h

end LipschitzHilbert

end

end OAI
