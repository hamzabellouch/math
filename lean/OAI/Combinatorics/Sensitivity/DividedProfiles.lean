import OAI.Combinatorics.Sensitivity.ProfileArithmetic

namespace OAI

/-! The four individual inequalities before taking the normalized maxima. -/

namespace Paper320

theorem divided_profiles_step {M r : ℝ} {n : ℕ}
    (hM : 0 < M) (hr : 0 ≤ r)
    {s₀ s₁ j₀ j₁ s₀' s₁' j₀' j₁' : ℝ}
    (hS₀ : s₀' ≤ 16 * s₀ + s₁ + 3 * j₁)
    (hS₁ : s₁' ≤ M ^ 2 * s₀ + r * s₁)
    (hJ₀ : j₀' ≤ 16 * s₀ + 3 * j₁)
    (hJ₁ : j₁' ≤ M ^ 2 * j₀ + r * s₁) :
    s₁' / M ^ (n + 2) ≤ (1 + r / M) * normalizedMax M n s₀ s₁ ∧
    s₀' / M ^ (n + 1) ≤
      (1 + 16 / M) * normalizedMax M n s₀ s₁ + 3 * normalizedMax M n j₀ j₁ ∧
    j₁' / M ^ (n + 2) ≤
      r / M * normalizedMax M n s₀ s₁ + normalizedMax M n j₀ j₁ ∧
    j₀' / M ^ (n + 1) ≤
      16 / M * normalizedMax M n s₀ s₁ + 3 * normalizedMax M n j₀ j₁ := by
  let u := normalizedMax M n s₀ s₁
  let v := normalizedMax M n j₀ j₁
  have hs₀ : s₀ ≤ u * M ^ n := le_normalizedMax_zero hM
  have hs₁ : s₁ ≤ u * (M ^ n * M) := by
    simpa only [pow_succ] using (le_normalizedMax_one (s₀ := s₀) (s₁ := s₁) (n := n) hM)
  have hj₀ : j₀ ≤ v * M ^ n := le_normalizedMax_zero hM
  have hj₁ : j₁ ≤ v * (M ^ n * M) := by
    simpa only [pow_succ] using (le_normalizedMax_one (s₀ := j₀) (s₁ := j₁) (n := n) hM)
  have a₀ := mul_le_mul_of_nonneg_left hs₀ (show (0 : ℝ) ≤ 16 by norm_num)
  have a₁ := mul_le_mul_of_nonneg_left hs₀ (sq_nonneg M)
  have b₀ := mul_le_mul_of_nonneg_left hj₀ (sq_nonneg M)
  have b₁ := mul_le_mul_of_nonneg_left hj₁ (show (0 : ℝ) ≤ 3 by norm_num)
  have c₁ := mul_le_mul_of_nonneg_left hs₁ hr
  have hrM : r / M * M = r := div_mul_cancel₀ _ hM.ne'
  have htM : (16 : ℝ) / M * M = 16 := div_mul_cancel₀ _ hM.ne'
  have hrMu := congrArg (fun z : ℝ => z * u * M ^ n * M) hrM
  have htMu := congrArg (fun z : ℝ => z * u * M ^ n) htM
  change s₁' / M ^ (n + 2) ≤ (1 + r / M) * u ∧
    s₀' / M ^ (n + 1) ≤ (1 + 16 / M) * u + 3 * v ∧
    j₁' / M ^ (n + 2) ≤ r / M * u + v ∧
    j₀' / M ^ (n + 1) ≤ 16 / M * u + 3 * v
  constructor
  · apply (div_le_iff₀ (pow_pos hM _)).mpr
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
    nlinarith
  constructor
  · apply (div_le_iff₀ (pow_pos hM _)).mpr
    rw [pow_succ]
    nlinarith
  constructor
  · apply (div_le_iff₀ (pow_pos hM _)).mpr
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
    nlinarith
  · apply (div_le_iff₀ (pow_pos hM _)).mpr
    rw [pow_succ]
    nlinarith

end Paper320

end OAI
