import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingWeightIdentification

namespace OAI

/-! # Uniform transfer between nearby expanding radii -/

open scoped ENNReal

namespace DefocusingNLS

noncomputable def expandingNearbyTransfer (a k : ℝ) (ha : 0 < a) (hk : 8 < k)
    (L M : {R : ℝ // 1 ≤ R}) : FourierL2 →L[ℂ] FourierL2 :=
  (expandingScaleTransfer a k 1 M.1 ha hk le_rfl M.2).comp
    (expandingInverseTransfer a k L.1 ha hk L.2)

theorem expandingNearbyTransfer_apply (a k : ℝ) (ha : 0 < a) (hk : 8 < k)
    (L M : {R : ℝ // 1 ≤ R}) (f : FourierL2) (n : frequencyLattice) :
    expandingNearbyTransfer a k ha hk L M f n =
      (expandingSobolevWeight a k M.1 n / expandingSobolevWeight a k L.1 n : ℝ) * f n := by
  change (expandingScaleRatio a k 1 M.1 n : ℂ) *
    ((expandingInverseRatio a k L.1 n : ℂ) * f n) = _
  unfold expandingScaleRatio expandingInverseRatio
  push_cast
  have hp := Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k 1 le_rfl n).ne'
  field_simp

private theorem weight_nearby_bound (a k : ℝ) (ha : 0 < a) (hk : 8 < k)
    (L M : {R : ℝ // 1 ≤ R}) (hML : M.1 ≤ 2 * L.1) (hLM : L.1 ≤ 2 * M.1)
    (n : frequencyLattice) :
    expandingSobolevWeight a k M.1 n ≤
      (2 ^ a + 2 ^ (k - 6)) * expandingSobolevWeight a k L.1 n := by
  have hLp : 0 < L.1 := lt_of_lt_of_le zero_lt_one L.2
  have hMp : 0 < M.1 := lt_of_lt_of_le zero_lt_one M.2
  let C : ℝ := 2 ^ a + 2 ^ (k - 6)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlo : M.1 ^ a ≤ C * L.1 ^ a := by
    calc
      _ ≤ (2 * L.1) ^ a := Real.rpow_le_rpow hMp.le hML ha.le
      _ = 2 ^ a * L.1 ^ a := Real.mul_rpow (by norm_num) hLp.le
      _ ≤ C * L.1 ^ a := by dsimp [C]; nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (k - 6), Real.rpow_pos_of_pos hLp a]
  have hhi : M.1 ^ (6 - k) ≤ C * L.1 ^ (6 - k) := by
    have hcomp := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < L.1 / 2)
      (show L.1 / 2 ≤ M.1 by linarith) (by linarith : 6 - k ≤ 0)
    have hid : (L.1 / 2) ^ (6 - k) = 2 ^ (k - 6) * L.1 ^ (6 - k) := by
      rw [Real.div_rpow hLp.le (by norm_num), div_eq_inv_mul,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring_nf
    calc
      _ ≤ (L.1 / 2) ^ (6 - k) := hcomp
      _ = 2 ^ (k - 6) * L.1 ^ (6 - k) := hid
      _ ≤ C * L.1 ^ (6 - k) := by dsimp [C]; nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) a, Real.rpow_pos_of_pos hLp (6 - k)]
  have sqr (R : ℝ) (hR : 0 ≤ R) (s : ℝ) : (R ^ s) ^ 2 = R ^ (2 * s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR]
    congr 1
    ring_nf
  have hs : expandingSobolevWeightSq a k M.1 n ≤ C ^ 2 * expandingSobolevWeightSq a k L.1 n := by
    unfold expandingSobolevWeightSq
    have hl := pow_le_pow_left₀ (Real.rpow_nonneg hMp.le a) hlo 2
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hMp.le (6 - k)) hhi 2
    rw [mul_pow, sqr M.1 hMp.le a, sqr L.1 hLp.le a] at hl
    rw [mul_pow, sqr M.1 hMp.le (6 - k), sqr L.1 hLp.le (6 - k)] at hh
    rw [show 2 * (6 - k) = 12 - 2 * k by ring] at hh
    calc
      _ ≤ C ^ 2 * L.1 ^ (2 * a) * (1 + ‖n‖ ^ 2) ^ (6 - a) +
          C ^ 2 * L.1 ^ (12 - 2 * k) * ‖n‖ ^ (2 * k) :=
        add_le_add (mul_le_mul_of_nonneg_right hl (by positivity))
          (mul_le_mul_of_nonneg_right hh (by positivity))
      _ = _ := by ring
  have hroot := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC] at hroot
  simpa only [expandingSobolevWeight, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ (2 * Real.pi) ^ 6)

theorem expandingNearbyTransfer_norm_le (a k : ℝ) (ha : 0 < a) (hk : 8 < k)
    (L M : {R : ℝ // 1 ≤ R}) (hML : M.1 ≤ 2 * L.1) (hLM : L.1 ≤ 2 * M.1) :
    ‖expandingNearbyTransfer a k ha hk L M‖ ≤ 2 ^ a + 2 ^ (k - 6) := by
  let C : ℝ := 2 ^ a + 2 ^ (k - 6)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  calc
    _ ≤ ‖C • f‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      rw [expandingNearbyTransfer_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (expandingSobolevWeight_pos a k M.1 M.2 n).le
          (expandingSobolevWeight_pos a k L.1 L.2 n).le)]
      simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (div_le_iff₀ (expandingSobolevWeight_pos a k L.1 L.2 n)).mpr
        (weight_nearby_bound a k ha hk L M hML hLM n)
    _ = C * ‖f‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]

end DefocusingNLS

end OAI
