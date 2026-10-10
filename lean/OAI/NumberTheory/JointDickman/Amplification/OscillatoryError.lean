import OAI.NumberTheory.JointDickman.Amplification.ParameterEstimates
import OAI.NumberTheory.JointDickman.Amplification.OscillatoryTests

namespace OAI

/-! # Explicit modulus and frequency losses in the coefficient estimate -/

namespace JointDickman

/-- A saving of 79 powers absorbs the modulus and frequency ranges in
manuscript equation (1), leaving 50 powers. -/
theorem oscillatory_error_bookkeeping {B q K X a b M N ξ : ℝ}
    (hB : 1 ≤ B) (hq : q ≤ B ^ (15 : ℝ))
    (hK : 0 ≤ K) (hX : 0 < X) (hb : 0 ≤ b) (hab : a ≤ b)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hξ : |ξ| ≤ B ^ (14 : ℝ)) :
    q * (K * B ^ (-79 : ℝ) * (b * X) *
        (2 * M + (N + 2 * Real.pi * |ξ| * M) / X * (b * X - a * X))) ≤
      (K * b * (2 * M + (N + 2 * Real.pi * M) * (b - a))) * X * B ^ (-50 : ℝ) := by
  have hB0 : 0 < B := by linarith
  have h14 : 1 ≤ B ^ (14 : ℝ) := Real.one_le_rpow hB (by norm_num)
  have hC : 0 ≤ 2 * M + (N + 2 * Real.pi * M) * (b - a) := by positivity
  have hfreq : N + 2 * Real.pi * |ξ| * M ≤ B ^ (14 : ℝ) * (N + 2 * Real.pi * M) := by
    have h1 := mul_le_mul_of_nonneg_left hξ (show 0 ≤ 2 * Real.pi * M by positivity)
    have h2 := mul_le_mul_of_nonneg_right h14 hN
    nlinarith
  have hbracket : 2 * M + (N + 2 * Real.pi * |ξ| * M) * (b - a) ≤
      B ^ (14 : ℝ) * (2 * M + (N + 2 * Real.pi * M) * (b - a)) := by
    have h1 := mul_le_mul_of_nonneg_right hfreq (sub_nonneg.mpr hab)
    have h2 := mul_le_mul_of_nonneg_right h14 (show 0 ≤ 2 * M by positivity)
    nlinarith
  have hcancel : (N + 2 * Real.pi * |ξ| * M) / X * (b * X - a * X) =
      (N + 2 * Real.pi * |ξ| * M) * (b - a) := by
    field_simp
  rw [hcancel]
  calc
    _ ≤ B ^ (15 : ℝ) * (K * B ^ (-79 : ℝ) * (b * X) *
        (B ^ (14 : ℝ) * (2 * M + (N + 2 * Real.pi * M) * (b - a)))) := by
      apply mul_le_mul hq
      · exact mul_le_mul_of_nonneg_left hbracket (by positivity)
      · positivity
      · positivity
    _ = _ := by
      have hp : B ^ (15 : ℝ) * B ^ (-79 : ℝ) * B ^ (14 : ℝ) = B ^ (-50 : ℝ) := by
        rw [← Real.rpow_add hB0, ← Real.rpow_add hB0]
        norm_num
      calc
        _ = (K * b * (2 * M + (N + 2 * Real.pi * M) * (b - a))) * X *
            (B ^ (15 : ℝ) * B ^ (-79 : ℝ) * B ^ (14 : ℝ)) := by ring
        _ = _ := by rw [hp]

end JointDickman

end OAI
