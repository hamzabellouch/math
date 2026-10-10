import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingQuadraticWeight

namespace OAI

/-! # A uniformly bounded multiplier representing two physical derivatives -/

open scoped ENNReal

namespace DefocusingNLS

noncomputable def expandingQuadraticRatio (a k L : ℝ) (n : frequencyLattice) : ℝ :=
  (‖n‖ / L) ^ 2 * expandingSobolevWeight a k L n / expandingSobolevWeight a (k + 2) L n

theorem expandingQuadraticRatio_bounds (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (n : frequencyLattice) :
    0 ≤ expandingQuadraticRatio a k L n ∧
      expandingQuadraticRatio a k L n ≤ Real.sqrt (2 ^ (6 - a) + 1) := by
  constructor
  · exact div_nonneg (mul_nonneg (sq_nonneg _) (expandingSobolevWeight_pos a k L hL n).le)
      (expandingSobolevWeight_pos a (k + 2) L hL n).le
  · exact (div_le_iff₀ (expandingSobolevWeight_pos a (k + 2) L hL n)).mpr
      (expandingSobolevWeight_quadratic a k L ha ha1 hk hL n)

noncomputable def expandingQuadraticVector (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) : FourierL2 :=
  ⟨fun n => (expandingQuadraticRatio a k L n : ℂ) * f n, by
    apply (lp.memℓp ((Real.sqrt (2 ^ (6 - a) + 1) : ℝ) • f)).mono'
    intro n
    simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs, norm_mul,
      Complex.norm_real, abs_of_nonneg (expandingQuadraticRatio_bounds a k L ha ha1 hk hL n).1,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (expandingQuadraticRatio_bounds a k L ha ha1 hk hL n).2
      (norm_nonneg _)⟩

theorem expandingQuadraticVector_norm (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) :
    ‖expandingQuadraticVector a k L ha ha1 hk hL f‖ ≤ Real.sqrt (2 ^ (6 - a) + 1) * ‖f‖ := by
  calc
    _ ≤ ‖(Real.sqrt (2 ^ (6 - a) + 1) : ℝ) • f‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      change ‖(expandingQuadraticRatio a k L n : ℂ) * f n‖ ≤
        ‖Real.sqrt (2 ^ (6 - a) + 1) • f n‖
      simp only [norm_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (expandingQuadraticRatio_bounds a k L ha ha1 hk hL n).1,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_right (expandingQuadraticRatio_bounds a k L ha ha1 hk hL n).2
        (norm_nonneg _)
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem expandingQuadraticVector_coefficient (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) (n : frequencyLattice) :
    expandingFourierCoefficient a k L (expandingQuadraticVector a k L ha ha1 hk hL f) n =
      ((‖n‖ / L) ^ 2 : ℝ) * expandingFourierCoefficient a (k + 2) L f n := by
  change (((expandingSobolevWeight a k L n)⁻¹ : ℝ) : ℂ) *
    (((expandingQuadraticRatio a k L n : ℝ) : ℂ) * f n) = _
  unfold expandingQuadraticRatio expandingFourierCoefficient
  push_cast
  have hw : (expandingSobolevWeight a k L n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k L hL n).ne'
  field_simp

end DefocusingNLS

end OAI
