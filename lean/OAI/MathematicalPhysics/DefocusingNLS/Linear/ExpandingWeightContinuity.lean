import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingScaleTransfer

namespace OAI

/-! # Uniform continuity estimates for the exact expanding weights

The weight is the Euclidean norm of two scalar power components.  This gives
one frequency-independent modulus of continuity for the scale-transfer map.
-/

namespace DefocusingNLS

private noncomputable def expandingWeightProfile (a k L : ℝ) (n : frequencyLattice) : ℂ :=
  ⟨L ^ a * Real.sqrt ((1 + ‖n‖ ^ 2) ^ (6 - a)),
    L ^ (6 - k) * Real.sqrt (‖n‖ ^ (2 * k))⟩

private theorem norm_expandingWeightProfile (a k L : ℝ) (hL : 1 ≤ L)
    (n : frequencyLattice) :
    ‖expandingWeightProfile a k L n‖ = Real.sqrt (expandingSobolevWeightSq a k L n) := by
  have hlow : (L ^ a) ^ 2 = L ^ (2 * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ L)]
    congr 1
    ring
  have hhigh : (L ^ (6 - k)) ^ 2 = L ^ (12 - 2 * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ L)]
    congr 1
    ring
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  congr 1
  change (L ^ a * Real.sqrt ((1 + ‖n‖ ^ 2) ^ (6 - a))) ^ 2 +
    (L ^ (6 - k) * Real.sqrt (‖n‖ ^ (2 * k))) ^ 2 = _
  rw [mul_pow, mul_pow, hlow, hhigh,
    Real.sq_sqrt (by positivity : 0 ≤ (1 + ‖n‖ ^ 2) ^ (6 - a)),
    Real.sq_sqrt (by positivity : 0 ≤ ‖n‖ ^ (2 * k))]
  rfl

private theorem expandingSobolevWeight_eq_profile (a k L : ℝ) (hL : 1 ≤ L)
    (n : frequencyLattice) :
    expandingSobolevWeight a k L n = (2 * Real.pi) ^ 6 * ‖expandingWeightProfile a k L n‖ := by
  rw [norm_expandingWeightProfile a k L hL n]
  rfl

/-- One modulus controls every Fourier weight relative to the radius-one weight. -/
theorem expandingSobolevWeight_difference_le (a k L M : ℝ)
    (hL : 1 ≤ L) (hM : 1 ≤ M) (n : frequencyLattice) :
    |expandingSobolevWeight a k L n - expandingSobolevWeight a k M n| ≤
      (|L ^ a - M ^ a| + |L ^ (6 - k) - M ^ (6 - k)|) *
        expandingSobolevWeight a k 1 n := by
  let A := Real.sqrt ((1 + ‖n‖ ^ 2) ^ (6 - a))
  let B := Real.sqrt (‖n‖ ^ (2 * k))
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hA1 : A ≤ ‖expandingWeightProfile a k 1 n‖ := by
    have h := Complex.abs_re_le_norm (expandingWeightProfile a k 1 n)
    have hre : (expandingWeightProfile a k 1 n).re = A := by
      simp only [expandingWeightProfile, Real.one_rpow, one_mul]; rfl
    rw [hre] at h
    simpa only [abs_of_nonneg hA] using h
  have hB1 : B ≤ ‖expandingWeightProfile a k 1 n‖ := by
    have h := Complex.abs_im_le_norm (expandingWeightProfile a k 1 n)
    have him : (expandingWeightProfile a k 1 n).im = B := by
      simp only [expandingWeightProfile, Real.one_rpow, one_mul]; rfl
    rw [him] at h
    simpa only [abs_of_nonneg hB] using h
  have hdiff : ‖expandingWeightProfile a k L n - expandingWeightProfile a k M n‖ ≤
      |L ^ a - M ^ a| * A + |L ^ (6 - k) - M ^ (6 - k)| * B := by
    convert Complex.norm_le_abs_re_add_abs_im
      (expandingWeightProfile a k L n - expandingWeightProfile a k M n) using 1
    simp only [expandingWeightProfile, Complex.sub_re, Complex.sub_im]
    rw [← sub_mul, ← sub_mul, abs_mul, abs_mul,
      abs_of_nonneg hA, abs_of_nonneg hB]
  have hnorm : |‖expandingWeightProfile a k L n‖ - ‖expandingWeightProfile a k M n‖| ≤
      (|L ^ a - M ^ a| + |L ^ (6 - k) - M ^ (6 - k)|) *
        ‖expandingWeightProfile a k 1 n‖ := by
    apply (abs_norm_sub_norm_le _ _).trans (hdiff.trans _)
    nlinarith [mul_le_mul_of_nonneg_left hA1 (abs_nonneg (L ^ a - M ^ a)),
      mul_le_mul_of_nonneg_left hB1 (abs_nonneg (L ^ (6 - k) - M ^ (6 - k)))]
  rw [expandingSobolevWeight_eq_profile a k L hL n,
    expandingSobolevWeight_eq_profile a k M hM n,
    expandingSobolevWeight_eq_profile a k 1 le_rfl n, ← mul_sub, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ 6)]
  calc
    _ ≤ (2 * Real.pi) ^ 6 *
        ((|L ^ a - M ^ a| + |L ^ (6 - k) - M ^ (6 - k)|) *
          ‖expandingWeightProfile a k 1 n‖) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

/-- The diagonal transfer coefficients have a common modulus in the scale. -/
theorem expandingScaleRatio_difference_le (a k L M : ℝ)
    (hL : 1 ≤ L) (hM : 1 ≤ M) (n : frequencyLattice) :
    |expandingScaleRatio a k 1 L n - expandingScaleRatio a k 1 M n| ≤
      |L ^ a - M ^ a| + |L ^ (6 - k) - M ^ (6 - k)| := by
  unfold expandingScaleRatio
  rw [← sub_div, abs_div,
    abs_of_pos (expandingSobolevWeight_pos a k 1 le_rfl n)]
  apply (div_le_iff₀ (expandingSobolevWeight_pos a k 1 le_rfl n)).2
  exact expandingSobolevWeight_difference_le a k L M hL hM n

end DefocusingNLS

end OAI
