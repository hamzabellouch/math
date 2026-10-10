import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PolynomialConstantBounds

namespace OAI

/-! Inverse-polynomial hopping scales give polynomial target ranges for
all polynomially bounded positive spin coefficients. -/

noncomputable section
namespace ContinuumCoulomb

theorem localizedCoulombProfile_zero_positive {freq : ℝ} (hfreq : 0 < freq) :
    0 < localizedCoulombProfile freq 0 := by
  unfold localizedCoulombProfile
  rw [zero_smul, localizedCoulombProfileAt_eq]
  exact localizedCoulombCoeff_positive hfreq 0 0

theorem exists_coulomb_target_polynomial_bounds {freq : ℝ} (hfreq : 0 < freq) (A B : ℕ) :
    ∃ L : ℕ, 0 < L ∧ ∀ N : ℝ, 2 ≤ N → ∀ K : ℝ,
      (N ^ A)⁻¹ ≤ K → K ≤ N ^ A →
      (N ^ (B + A + L))⁻¹ ≤ (N ^ B)⁻¹ * Real.sqrt (K * localizedGramConstant freq) ∧
      (N ^ B)⁻¹ * Real.sqrt (K * localizedCoulombProfile freq 0) ≤ N ^ (B + A + L) := by
  obtain ⟨L, hL, hconstants⟩ := exists_polynomial_constant_bounds
    (Real.sqrt_pos.mpr (localizedGramConstant_positive hfreq))
    (Real.sqrt (localizedCoulombProfile freq 0))
  refine ⟨L, hL, fun N hN K hKlo hKhi => ?_⟩
  have hN₁ : 1 ≤ N := by linarith
  have hNp : 0 < N := by linarith
  have hK : 0 ≤ K := (inv_nonneg.mpr (pow_nonneg hNp.le A)).trans hKlo
  obtain ⟨hrootlo, hroothi⟩ := sqrt_polynomial_bounds hN₁ hKlo hKhi
  obtain ⟨hclo, hUhi⟩ := hconstants N hN
  have hτ : 0 ≤ (N ^ B)⁻¹ := inv_nonneg.mpr (pow_nonneg hNp.le B)
  constructor
  · rw [Real.sqrt_mul hK]
    calc
      _ = (N ^ B)⁻¹ * ((N ^ A)⁻¹ * (N ^ L)⁻¹) := by
        rw [pow_add, pow_add]
        simp only [mul_inv_rev]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul hrootlo hclo (inv_nonneg.mpr (pow_nonneg hNp.le L)) (Real.sqrt_nonneg K)) hτ
  · have hτ₁ : (N ^ B)⁻¹ ≤ 1 := (inv_le_one₀ (pow_pos hNp B)).mpr (one_le_pow₀ hN₁)
    calc
      _ ≤ Real.sqrt (K * localizedCoulombProfile freq 0) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hτ₁
          (Real.sqrt_nonneg (K * localizedCoulombProfile freq 0))
      _ = Real.sqrt K * Real.sqrt (localizedCoulombProfile freq 0) := Real.sqrt_mul hK _
      _ ≤ N ^ A * N ^ L := mul_le_mul hroothi hUhi (Real.sqrt_nonneg _) (pow_nonneg hNp.le A)
      _ = N ^ (A + L) := (pow_add N A L).symm
      _ ≤ _ := pow_le_pow_right₀ hN₁ (by omega)

theorem exists_inverse_polynomial_coulomb_calibration {freq ε : ℝ} (hfreq : 0 < freq)
    (hε : 0 < ε) (hε₁ : ε < 1) (A B : ℕ) :
    ∃ k : ℕ, 0 < k ∧ ∀ N : ℝ, 2 ≤ N →
      5 ≤ (1 - ε) * ((k : ℝ) * Real.log N) ∧
      ∀ K : ℝ, (N ^ A)⁻¹ ≤ K → K ≤ N ^ A →
        ∃ d ∈ Set.Icc ((1 - ε) * ((k : ℝ) * Real.log N))
          ((1 + ε) * ((k : ℝ) * Real.log N)),
          N ^ k * planarHopping d = coulombHoppingTarget freq (N ^ B)⁻¹ K d := by
  obtain ⟨L, _, hrange⟩ := exists_coulomb_target_polynomial_bounds hfreq A B
  obtain ⟨k, hk, hcal⟩ := exists_uniform_coulomb_calibration hfreq hε hε₁ (B + A + L) 0
  refine ⟨k, hk, fun N hN => ⟨(hcal N hN).1, fun K hKlo hKhi => ?_⟩⟩
  have hNp : 0 < N := by linarith
  obtain ⟨hlo, hhi⟩ := hrange N hN K hKlo hKhi
  exact (hcal N hN).2.2.1 (N ^ B)⁻¹ K (by positivity)
    ((inv_nonneg.mpr (pow_nonneg hNp.le A)).trans hKlo) hlo hhi

end ContinuumCoulomb

end

end OAI
