import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingEnergyComponents

namespace OAI

/-! # Exact transport of the two expanding-torus energies -/

namespace DefocusingNLS

theorem expandingRadius_rpow (L s p : ℝ) (hL : 1 ≤ L) :
    expandingRadius L s ^ p = Real.exp (p * s / 2) * L ^ p := by
  unfold expandingRadius
  rw [Real.mul_rpow (by linarith : 0 ≤ L) (Real.exp_pos _).le, ← Real.exp_mul]
  rw [mul_comm (L ^ p)]
  congr 2
  ring

theorem expandingScaleRatio_sq (a k L M : ℝ) (hL : 1 ≤ L) (hM : 1 ≤ M)
    (n : frequencyLattice) :
    expandingScaleRatio a k L M n ^ 2 =
      expandingSobolevWeightSq a k M n / expandingSobolevWeightSq a k L n := by
  rw [expandingScaleRatio, div_pow, expandingSobolevWeight_sq a k M hM,
    expandingSobolevWeight_sq a k L hL]
  have hC : (2 * Real.pi) ^ 12 ≠ 0 := by positivity
  field_simp

theorem expandingLowFraction_transport (a k L s : ℝ) (hL : 1 ≤ L)
    (hs : 0 ≤ s) (n : frequencyLattice) :
    expandingLowFraction a k (expandingRadius L s) n *
        expandingScaleRatio a k L (expandingRadius L s) n ^ 2 =
      Real.exp (a * s) * expandingLowFraction a k L n := by
  have hM := hL.trans (expandingRadius_ge L s hL hs)
  rw [expandingScaleRatio_sq a k L _ hL hM]
  unfold expandingLowFraction
  rw [expandingRadius_rpow L s (2 * a) hL,
    show 2 * a * s / 2 = a * s by ring]
  have hW := (expandingSobolevWeightSq_pos a k L hL n).ne'
  have hV := (expandingSobolevWeightSq_pos a k _ hM n).ne'
  field_simp

theorem expandingHighFraction_transport (a k L s : ℝ) (hL : 1 ≤ L)
    (hs : 0 ≤ s) (n : frequencyLattice) :
    (1 - expandingLowFraction a k (expandingRadius L s) n) *
        expandingScaleRatio a k L (expandingRadius L s) n ^ 2 =
      Real.exp ((6 - k) * s) * (1 - expandingLowFraction a k L n) := by
  have hM := hL.trans (expandingRadius_ge L s hL hs)
  rw [expandingScaleRatio_sq a k L _ hL hM,
    expandingHighFraction_eq a k _ hM, expandingHighFraction_eq a k L hL,
    expandingRadius_rpow L s (12 - 2 * k) hL,
    show (12 - 2 * k) * s / 2 = (6 - k) * s by ring]
  have hW := (expandingSobolevWeightSq_pos a k L hL n).ne'
  have hV := (expandingSobolevWeightSq_pos a k _ hM n).ne'
  field_simp

theorem expandingFreeStep_mode_norm_sq (a b k L s : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hs : 0 ≤ s)
    (f : FourierL2) (n : frequencyLattice) :
    ‖expandingFreeStep a b k L s ha hk hL hs f n‖ ^ 2 =
      Real.exp (-2 * a * s) * expandingScaleRatio a k L (expandingRadius L s) n ^ 2 *
        ‖f n‖ ^ 2 := by
  change ‖expandingFreeAmplitude a b s *
    ((expandingScaleRatio a k L (expandingRadius L s) n : ℂ) *
      (schrodingerMultiplier (expandingFreeTime L s) n * f n))‖ ^ 2 = _
  rw [norm_mul, norm_mul, norm_mul, expandingFreeAmplitude_norm,
    schrodingerMultiplier_norm, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (expandingScaleRatio_nonneg a k L _ hL (expandingRadius_ge L s hL hs) n),
    mul_pow, mul_pow, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (-a * s) = -2 * a * s by ring]
  ring

theorem expandingLowEnergy_free (a b k L s : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hs : 0 ≤ s) (f : FourierL2) :
    ‖expandingLowEnergy a k (expandingRadius L s)
        (hL.trans (expandingRadius_ge L s hL hs))
        (expandingFreeStep a b k L s ha hk hL hs f)‖ ^ 2 =
      Real.exp (-a * s) * ‖expandingLowEnergy a k L hL f‖ ^ 2 := by
  simp only [expandingLowEnergy, fourierEnergyComponent_norm_sq]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [expandingFreeStep_mode_norm_sq]
  calc
    _ = (Real.exp (-2 * a * s) *
      (expandingLowFraction a k (expandingRadius L s) n *
        expandingScaleRatio a k L (expandingRadius L s) n ^ 2)) * ‖f n‖ ^ 2 := by ring
    _ = _ := by
      rw [expandingLowFraction_transport a k L s hL hs, ← mul_assoc, ← Real.exp_add,
        show -2 * a * s + a * s = -a * s by ring]
      ring

theorem expandingHighEnergy_free (a b k L s : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hs : 0 ≤ s) (f : FourierL2) :
    ‖expandingHighEnergy a k (expandingRadius L s)
        (hL.trans (expandingRadius_ge L s hL hs))
        (expandingFreeStep a b k L s ha hk hL hs f)‖ ^ 2 =
      Real.exp ((6 - 2 * a - k) * s) * ‖expandingHighEnergy a k L hL f‖ ^ 2 := by
  simp only [expandingHighEnergy, fourierEnergyComponent_norm_sq]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [expandingFreeStep_mode_norm_sq]
  calc
    _ = (Real.exp (-2 * a * s) *
      ((1 - expandingLowFraction a k (expandingRadius L s) n) *
        expandingScaleRatio a k L (expandingRadius L s) n ^ 2)) * ‖f n‖ ^ 2 := by ring
    _ = _ := by
      rw [expandingHighFraction_transport a k L s hL hs, ← mul_assoc, ← Real.exp_add,
        show -2 * a * s + (6 - k) * s = (6 - 2 * a - k) * s by ring]
      ring

theorem expandingFreeEnergy_norm_sq (a b k L s : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hs : 0 ≤ s) (f : FourierL2) :
    ‖expandingFreeStep a b k L s ha hk hL hs f‖ ^ 2 =
      Real.exp (-a * s) * ‖expandingLowEnergy a k L hL f‖ ^ 2 +
        Real.exp ((6 - 2 * a - k) * s) * ‖expandingHighEnergy a k L hL f‖ ^ 2 := by
  rw [expandingEnergy_norm_sq a k (expandingRadius L s)
    (hL.trans (expandingRadius_ge L s hL hs)),
    expandingLowEnergy_free, expandingHighEnergy_free]

end DefocusingNLS

end OAI
