import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace OAI

namespace MatroidProphet

noncomputable section

def weightBase : ℝ := 2 ^ 32
def densityThreshold : ℝ := 2 ^ 100
def thinningRate : ℝ := ((2 : ℝ) ^ 140)⁻¹
def exitThreshold : ℝ := ((2 : ℝ) ^ 12)⁻¹
def retainedFraction : ℝ := ((2 : ℝ) ^ 16)⁻¹

theorem constants_positive : 0 < weightBase ∧ 0 < densityThreshold ∧
    0 < thinningRate ∧ 0 < exitThreshold ∧ 0 < retainedFraction := by
  norm_num [weightBase, densityThreshold, thinningRate, exitThreshold, retainedFraction]

theorem error_constant :
    ((2 : ℝ) ^ 23)⁻¹ + thinningRate * densityThreshold +
      (1 + thinningRate * densityThreshold) / (weightBase - 1) < ((2 : ℝ) ^ 21)⁻¹ := by
  norm_num [thinningRate, densityThreshold, weightBase]

theorem retained_fraction_slack :
    retainedFraction / 8 ≤ retainedFraction / 4 - ((2 : ℝ) ^ 21)⁻¹ := by
  norm_num [retainedFraction]

theorem hidden_fraction_exact :
    thinningRate * retainedFraction / (32 * densityThreshold * weightBase) =
      ((2 : ℝ) ^ 293)⁻¹ := by
  rw [show 293 = 140 + 153 from rfl, pow_add]
  norm_num [thinningRate, retainedFraction, densityThreshold, weightBase]

theorem public_fraction_slack : ((2 : ℝ) ^ 310)⁻¹ ≤ ((2 : ℝ) ^ 293)⁻¹ := by
  rw [show 310 = 155 + 155 from rfl, show 293 = 140 + 153 from rfl, pow_add, pow_add]
  norm_num

theorem branch_mixture_lower (W maximumWeight mainPayoff maximumPayoff : ℝ)
    (hW : 0 ≤ W) (hmw : 0 ≤ maximumWeight) (hmain : 0 ≤ mainPayoff)
    (hmax : maximumWeight / 4 ≤ maximumPayoff)
    (hsmall : maximumWeight ≤ W / (8 * densityThreshold) →
      thinningRate * retainedFraction / (16 * densityThreshold) * W ≤ mainPayoff) :
    thinningRate * retainedFraction / (32 * densityThreshold) * W ≤
      (mainPayoff + maximumPayoff) / 2 := by
  by_cases hm : maximumWeight ≤ W / (8 * densityThreshold)
  · have hs := hsmall hm
    have hz : 0 ≤ maximumPayoff := by linarith
    norm_num [thinningRate, retainedFraction, densityThreshold] at hs ⊢
    linarith
  · have hm' : W / (8 * densityThreshold) < maximumWeight := lt_of_not_ge hm
    have hc : thinningRate * retainedFraction / (32 * densityThreshold) ≤
        1 / (64 * densityThreshold) := by
      norm_num [thinningRate, retainedFraction, densityThreshold]
    have hcW := mul_le_mul_of_nonneg_right hc hW
    norm_num [densityThreshold] at hm' hcW ⊢
    linarith

end

end MatroidProphet

end OAI
