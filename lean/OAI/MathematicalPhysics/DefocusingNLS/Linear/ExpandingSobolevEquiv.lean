import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSobolevComparison

namespace OAI

/-! # Coefficient-preserving identification of fixed expanding and Sobolev norms -/

open scoped ENNReal

namespace DefocusingNLS

private noncomputable def boundedRealDiagonalVector (c : ℝ) (hc : 0 ≤ c)
    (w : frequencyLattice → ℝ) (hw : ∀ n, 0 ≤ w n ∧ w n ≤ c) (f : FourierL2) : FourierL2 :=
  ⟨fun n => (w n : ℂ) * f n, by
    apply (lp.memℓp (c • f)).mono'
    intro n
    simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
      norm_mul, Complex.norm_real, abs_of_nonneg (hw n).1, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_right (hw n).2 (norm_nonneg _)⟩

private theorem boundedRealDiagonalVector_norm_le (c : ℝ) (hc : 0 ≤ c)
    (w : frequencyLattice → ℝ) (hw : ∀ n, 0 ≤ w n ∧ w n ≤ c) (f : FourierL2) :
    ‖boundedRealDiagonalVector c hc w hw f‖ ≤ c * ‖f‖ := by
  calc
    _ ≤ ‖c • f‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      change ‖(w n : ℂ) * f n‖ ≤ ‖c • f n‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw n).1,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_right (hw n).2 (norm_nonneg _)
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]

private noncomputable def boundedRealDiagonal (c : ℝ) (hc : 0 ≤ c)
    (w : frequencyLattice → ℝ) (hw : ∀ n, 0 ≤ w n ∧ w n ≤ c) : FourierL2 →L[ℂ] FourierL2 :=
  LinearMap.mkContinuous
    { toFun := boundedRealDiagonalVector c hc w hw
      map_add' := by
        intro f g
        ext n
        change (w n : ℂ) * (f n + g n) = (w n : ℂ) * f n + (w n : ℂ) * g n
        ring
      map_smul' := by
        intro z f
        ext n
        change (w n : ℂ) * (z * f n) = z * ((w n : ℂ) * f n)
        ring }
    c (boundedRealDiagonalVector_norm_le c hc w hw)

noncomputable def standardSobolevWeight (k : ℝ) (n : frequencyLattice) : ℝ :=
  (1 + ‖n‖ ^ 2) ^ (k / 2)

theorem standardSobolevWeight_pos (k : ℝ) (n : frequencyLattice) :
    0 < standardSobolevWeight k n := Real.rpow_pos_of_pos (by positivity) _

noncomputable def expandingToSobolevRatio (a k : ℝ) (n : frequencyLattice) : ℝ :=
  standardSobolevWeight k n / expandingSobolevWeight a k 1 n

noncomputable def sobolevToExpandingRatio (a k : ℝ) (n : frequencyLattice) : ℝ :=
  expandingSobolevWeight a k 1 n / standardSobolevWeight k n

private theorem expandingToSobolevRatio_bounds (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (n : frequencyLattice) :
    0 ≤ expandingToSobolevRatio a k n ∧
      expandingToSobolevRatio a k n ≤ ((2 * Real.pi) ^ 6)⁻¹ * Real.sqrt (2 ^ k) := by
  constructor
  · exact (div_pos (standardSobolevWeight_pos k n)
      (expandingSobolevWeight_pos a k 1 le_rfl n)).le
  · apply (div_le_iff₀ (expandingSobolevWeight_pos a k 1 le_rfl n)).mpr
    exact standard_le_expandingSobolevWeight_one a k ha1 hk n

private theorem sobolevToExpandingRatio_bounds (a k : ℝ) (ha : 0 < a) (hk : 8 < k)
    (n : frequencyLattice) :
    0 ≤ sobolevToExpandingRatio a k n ∧
      sobolevToExpandingRatio a k n ≤ (2 * Real.pi) ^ 6 * Real.sqrt 2 := by
  constructor
  · exact (div_pos (expandingSobolevWeight_pos a k 1 le_rfl n)
      (standardSobolevWeight_pos k n)).le
  · apply (div_le_iff₀ (standardSobolevWeight_pos k n)).mpr
    exact expandingSobolevWeight_one_le_standard a k ha hk n

/-- The physical Fourier coefficients are unchanged; only their weights change. -/
noncomputable def expandingToSobolev (a k : ℝ) (ha1 : a < 1) (hk : 8 < k) :
    FourierL2 →L[ℂ] FourierL2 :=
  boundedRealDiagonal (((2 * Real.pi) ^ 6)⁻¹ * Real.sqrt (2 ^ k)) (by positivity)
    (expandingToSobolevRatio a k) (expandingToSobolevRatio_bounds a k ha1 hk)

noncomputable def sobolevToExpanding (a k : ℝ) (ha : 0 < a) (hk : 8 < k) :
    FourierL2 →L[ℂ] FourierL2 :=
  boundedRealDiagonal ((2 * Real.pi) ^ 6 * Real.sqrt 2) (by positivity)
    (sobolevToExpandingRatio a k) (sobolevToExpandingRatio_bounds a k ha hk)

@[simp] theorem expandingToSobolev_apply (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (f : FourierL2) (n : frequencyLattice) :
    expandingToSobolev a k ha1 hk f n = (expandingToSobolevRatio a k n : ℂ) * f n := rfl

@[simp] theorem sobolevToExpanding_apply (a k : ℝ) (ha : 0 < a) (hk : 8 < k)
    (f : FourierL2) (n : frequencyLattice) :
    sobolevToExpanding a k ha hk f n = (sobolevToExpandingRatio a k n : ℂ) * f n := rfl

theorem sobolevToExpanding_expandingToSobolev (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : FourierL2) :
    sobolevToExpanding a k ha hk (expandingToSobolev a k ha1 hk f) = f := by
  ext n
  simp only [sobolevToExpanding_apply, expandingToSobolev_apply,
    sobolevToExpandingRatio, expandingToSobolevRatio, Complex.ofReal_div]
  have hs : (standardSobolevWeight k n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (standardSobolevWeight_pos k n).ne'
  have he : (expandingSobolevWeight a k 1 n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k 1 le_rfl n).ne'
  field_simp

theorem expandingToSobolev_sobolevToExpanding (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : FourierL2) :
    expandingToSobolev a k ha1 hk (sobolevToExpanding a k ha hk f) = f := by
  ext n
  simp only [sobolevToExpanding_apply, expandingToSobolev_apply,
    sobolevToExpandingRatio, expandingToSobolevRatio, Complex.ofReal_div]
  have hs : (standardSobolevWeight k n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (standardSobolevWeight_pos k n).ne'
  have he : (expandingSobolevWeight a k 1 n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k 1 le_rfl n).ne'
  field_simp

noncomputable def expandingSobolevEquiv (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) : FourierL2 ≃L[ℂ] FourierL2 where
  toLinearEquiv :=
    { toLinearMap := (expandingToSobolev a k ha1 hk).toLinearMap
      invFun := sobolevToExpanding a k ha hk
      left_inv := sobolevToExpanding_expandingToSobolev a k ha ha1 hk
      right_inv := expandingToSobolev_sobolevToExpanding a k ha ha1 hk }
  continuous_toFun := (expandingToSobolev a k ha1 hk).continuous
  continuous_invFun := (sobolevToExpanding a k ha hk).continuous

theorem expandingToSobolev_coefficient (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (f : FourierL2) (n : frequencyLattice) :
    sobolevFourierCoefficient k (expandingToSobolev a k ha1 hk f) n =
      expandingFourierCoefficient a k 1 f n := by
  have hp := (standardSobolevWeight_pos k n).ne'
  have hw : (1 + ‖n‖ ^ 2) ^ (-k / 2) = (standardSobolevWeight k n)⁻¹ := by
    rw [standardSobolevWeight, show -k / 2 = -(k / 2) by ring, Real.rpow_neg (by positivity)]
  simp only [sobolevFourierCoefficient, expandingToSobolev_apply, hw, Complex.real_smul,
    expandingToSobolevRatio, expandingFourierCoefficient, Complex.ofReal_div, Complex.ofReal_inv]
  have hc : (standardSobolevWeight k n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp
  field_simp

end DefocusingNLS

end OAI
