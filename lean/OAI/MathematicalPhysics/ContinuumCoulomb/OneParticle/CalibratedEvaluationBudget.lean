import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedEvaluationParameters

namespace OAI

/-! A fixed polynomial accuracy schedule for the calibrated hopping
residual. The square-root input uses quadratic precision in the requested
inverse error, rather than assuming a spectral gap for numerical samples. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedEvaluation

theorem hopping_budget (scale P : ℕ) :
    (scale : ℝ) * ((hoppingPrecision scale P : ℝ) + 1)⁻¹ ≤
      (4 * ((P : ℝ) + 1))⁻¹ := by
  have hP : 0 < (P : ℝ) + 1 := by positivity
  have hprec : (hoppingPrecision scale P : ℝ) =
      4 * ((scale : ℝ) + 1) * ((P : ℝ) + 1) := by
    simp only [hoppingPrecision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  rw [hprec]
  apply (mul_inv_le_iff₀ (by positivity)).mpr
  apply (le_inv_mul_iff₀ (by positivity : (0 : ℝ) < 4 * (P + 1))).mpr
  nlinarith

theorem root_budget (P : ℕ) :
    (2 : ℝ)⁻¹ ^ rootPrecision P ≤ (4 * ((P : ℝ) + 1))⁻¹ := by
  apply (CoulombQuadratureSchedule.dyadic_le_inverse _).trans
  apply inv_anti₀ (by positivity)
  simp only [rootPrecision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  linarith [show (0 : ℝ) ≤ P from Nat.cast_nonneg _]

theorem coulomb_root_budget (N P : ℕ) {K : ℝ} (hKN : K ≤ N) :
    Real.sqrt (2 * K * ((coulombPrecision N P : ℝ) + 1)⁻¹) ≤
      (4 * ((P : ℝ) + 1))⁻¹ := by
  let S := (P : ℝ) + 1
  have hS : 0 < S := by dsimp only [S]; positivity
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hprec : (coulombPrecision N P : ℝ) = 64 * ((N : ℝ) + 1) * S ^ 2 := by
    simp only [coulombPrecision, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
      Nat.cast_pow, S]
  have hsmall : 2 * K * ((coulombPrecision N P : ℝ) + 1)⁻¹ ≤ ((4 * S)⁻¹) ^ 2 := by
    rw [hprec]
    apply (mul_inv_le_iff₀ (by positivity)).mpr
    have he : ((4 * S)⁻¹) ^ 2 * (64 * ((N : ℝ) + 1) * S ^ 2 + 1) =
        4 * ((N : ℝ) + 1) + ((4 * S)⁻¹) ^ 2 := by
      field_simp [hS.ne']
      ring
    rw [he]
    nlinarith [sq_nonneg ((4 * S)⁻¹)]
  exact (Real.sqrt_le_sqrt hsmall).trans_eq (by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) hS))])

end ContinuumCoulomb.CalibratedEvaluation

end

end OAI
