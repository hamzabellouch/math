import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalClock
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSobolevStrong

namespace OAI

/-! # Restoring the physical nonlinear Schrödinger equation

The normalization uses the exact relation `2 a m = 1`.  Both the amplitude
and the nonlinear coefficient are restored before changing time.
-/

namespace DefocusingNLS

theorem expandingPhysicalAmplitude_nonlinearity (a b k L s : ℝ)
    (hk : 6 < k) (hL : 0 < L) (m : ℕ) (ham : 2 * a * m = 1)
    (v : FourierL2) :
    (L ^ (-2 : ℝ) * Real.exp (-s)) • lowerSobolevInclusion
        (sobolevOddPower k hk m (expandingPhysicalAmplitude a b L s • v)) =
      expandingPhysicalAmplitude a b L s • lowerSobolevInclusion
        (sobolevOddPower k hk m v) := by
  rw [sobolevOddPower_smul_norm, map_smul, map_smul]
  have hq : (((L ^ (-2 : ℝ) * Real.exp (-s)) : ℝ) : ℂ) *
      ((‖expandingPhysicalAmplitude a b L s‖ ^ (2 * m) : ℝ) : ℂ) = 1 := by
    exact_mod_cast expandingPhysicalAmplitude_clock a b L s hL m ham
  ext n
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  calc
    _ = ((((L ^ (-2 : ℝ) * Real.exp (-s)) : ℝ) : ℂ) *
        ((‖expandingPhysicalAmplitude a b L s‖ ^ (2 * m) : ℝ) : ℂ)) *
          (expandingPhysicalAmplitude a b L s *
            lowerSobolevInclusion (sobolevOddPower k hk m v) n) := by ring
    _ = _ := by rw [hq, one_mul]

theorem hasDerivAt_expandingPhysicalAmplitude_curve (a b k L : ℝ)
    (hk : 6 < k) (hL : 0 < L) (m : ℕ) (ham : 2 * a * m = 1)
    (v : ℝ → FourierL2) (s : ℝ)
    (hv : HasDerivAt (fun t => lowerSobolevInclusion (v t))
      ((-(a : ℂ) + Complex.I * b) • lowerSobolevInclusion (v s) +
        (L ^ (-2 : ℝ) * Real.exp (-s)) • lowerSobolevGenerator (v s) +
        (-Complex.I) • lowerSobolevInclusion (sobolevOddPower k hk m (v s))) s) :
    let U := fun t => expandingPhysicalAmplitude a b L t • v t
    HasDerivAt (fun t => lowerSobolevInclusion (U t))
      ((L ^ (-2 : ℝ) * Real.exp (-s)) •
        (lowerSobolevGenerator (U s) -
          Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (U s)))) s := by
  intro U
  have h := (hasDerivAt_expandingPhysicalAmplitude a b L s).smul hv
  convert h using 1
  · funext t
    exact map_smul lowerSobolevInclusion _ _
  · have hN := expandingPhysicalAmplitude_nonlinearity a b k L s hk hL m ham (v s)
    dsimp [U]
    rw [smul_sub, smul_comm (L ^ (-2 : ℝ) * Real.exp (-s)) Complex.I, hN, map_smul]
    ext n
    simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_sub, Pi.sub_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    ring

theorem hasDerivAt_expandingPhysicalEquation (a b k L : ℝ)
    (hk : 6 < k) (hL : 0 < L) (m : ℕ) (ham : 2 * a * m = 1)
    (v : ℝ → FourierL2) (t : ℝ) (ht : 0 < 1 - L ^ 2 * t)
    (hv : HasDerivAt (fun s => lowerSobolevInclusion (v s))
      ((-(a : ℂ) + Complex.I * b) • lowerSobolevInclusion (v (expandingInverseClock L t)) +
        (L ^ (-2 : ℝ) * Real.exp (-expandingInverseClock L t)) •
          lowerSobolevGenerator (v (expandingInverseClock L t)) +
        (-Complex.I) • lowerSobolevInclusion
          (sobolevOddPower k hk m (v (expandingInverseClock L t))))
      (expandingInverseClock L t)) :
    let U := fun τ => expandingPhysicalAmplitude a b L (expandingInverseClock L τ) •
      v (expandingInverseClock L τ)
    HasDerivAt (fun τ => lowerSobolevInclusion (U τ))
      (lowerSobolevGenerator (U t) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (U t))) t := by
  intro U
  have h := (hasDerivAt_expandingPhysicalAmplitude_curve a b k L hk hL m ham
    v (expandingInverseClock L t) hv).scomp t (hasDerivAt_expandingInverseClock L t ht)
  apply h.congr_deriv
  rw [smul_smul, mul_comm, expandingInverseClock_derivative_cancel L t hL ht, one_smul]

end DefocusingNLS

end OAI
