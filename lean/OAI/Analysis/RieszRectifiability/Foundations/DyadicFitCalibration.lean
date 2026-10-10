import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.NeighboringFitErrors

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_dyadic_fit_calibration (n : ℕ) (b c : ℝ) (hc : 0 < c) :
    ∃ L : ℝ, 0 < L ∧ dyadicFitErrorConstant n b ≤ L ^ 2 * (c / 2) := by
  let q := 2 * dyadicFitErrorConstant n b / c
  have hq : 0 ≤ q := div_nonneg
    (mul_nonneg (by norm_num) (dyadicFitErrorConstant_pos n b).le) hc.le
  let L := 1 + Real.sqrt q
  have hL : 0 < L := by dsimp only [L]; positivity
  have hs : q ≤ L ^ 2 := by
    dsimp only [L]
    nlinarith [Real.sq_sqrt hq, Real.sqrt_nonneg q]
  refine ⟨L, hL, ?_⟩
  calc
    dyadicFitErrorConstant n b = q * (c / 2) := by dsimp only [q]; field_simp
    _ ≤ L ^ 2 * (c / 2) := mul_le_mul_of_nonneg_right hs (by positivity)

theorem calibrated_dyadic_joint_fit_error {n d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (P : ℕ → AffineSubspace ℝ (Ambient d)) (hP : ∀ i, IsAffineNPlane n (P i))
    (δ b L c : ℝ) (hcal : dyadicFitErrorConstant n b ≤ L ^ 2 * (c / 2)) (N : ℕ)
    (hfit : ∀ i ≤ N, (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ i),
      infDist x (P i : Set (Ambient d)) ^ 2 ∂μ) ≤
        2 * (δ * b ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n + 2)) (i : ℕ) (hi : i < N) :
    (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ i), jointPlaneFitError (P i) (P (i + 1)) x ∂μ) ≤
      (L * δ * (2 : ℝ) ^ i * b ^ i) ^ 2 * ((c / 2) * ((2 : ℝ) ^ i) ^ n) := by
  calc
    _ ≤ dyadicFitErrorConstant n b * (δ * b ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n + 2) :=
      dyadic_neighboring_joint_fit_error_bound μ P hP δ b N hfit i hi
    _ ≤ (L ^ 2 * (c / 2)) * (δ * b ^ i) ^ 2 * ((2 : ℝ) ^ i) ^ (n + 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcal (sq_nonneg _)) (by positivity)
    _ = _ := by rw [pow_add ((2 : ℝ) ^ i) n 2]; ring

theorem calibrated_dyadic_threshold_small (L δ b ε : ℝ)
    (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hb : 1 ≤ b) (N i : ℕ) (hi : i ≤ N)
    (hsmall : L * δ * b ^ N ≤ ε) :
    L * δ * (2 : ℝ) ^ i * b ^ i ≤ ε * (2 : ℝ) ^ i := by
  have hbpow : b ^ i ≤ b ^ N := pow_le_pow_right₀ hb hi
  calc
    L * δ * (2 : ℝ) ^ i * b ^ i = (L * δ * b ^ i) * (2 : ℝ) ^ i := by ring
    _ ≤ (L * δ * b ^ N) * (2 : ℝ) ^ i :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbpow (mul_nonneg hL hδ)) (by positivity)
    _ ≤ ε * (2 : ℝ) ^ i := mul_le_mul_of_nonneg_right hsmall (by positivity)

end

end RieszRectifiability

end OAI
