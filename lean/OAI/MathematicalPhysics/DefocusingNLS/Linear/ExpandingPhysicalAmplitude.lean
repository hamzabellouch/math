import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingModeEquation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevAmplitude

namespace OAI

/-! # The amplitude restoring physical Schrödinger time

For `2 a m = 1`, the factor below has precisely the nonlinear scaling
required by the clock `L⁻² (1 - exp(-s))`.
-/

namespace DefocusingNLS

noncomputable def expandingPhysicalAmplitude (a b L s : ℝ) : ℂ :=
  (L ^ (2 * a) : ℝ) * expandingFreeAmplitude (-a) (-b) s

theorem expandingPhysicalAmplitude_norm (a b L s : ℝ) (hL : 0 < L) :
    ‖expandingPhysicalAmplitude a b L s‖ = L ^ (2 * a) * Real.exp (a * s) := by
  rw [expandingPhysicalAmplitude, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL _), expandingFreeAmplitude_norm]
  simp only [neg_neg]

theorem hasDerivAt_expandingPhysicalAmplitude (a b L s : ℝ) :
    HasDerivAt (expandingPhysicalAmplitude a b L)
      (((a : ℂ) - Complex.I * b) * expandingPhysicalAmplitude a b L s) s := by
  have h := (hasDerivAt_expandingFreeAmplitude (-a) (-b) s).const_mul
    ((L ^ (2 * a) : ℝ) : ℂ)
  convert h using 1
  · rfl
  · unfold expandingPhysicalAmplitude
    push_cast
    ring

theorem expandingPhysicalAmplitude_power (a b L s : ℝ) (hL : 0 < L)
    (m : ℕ) (ham : 2 * a * m = 1) :
    ‖expandingPhysicalAmplitude a b L s‖ ^ (2 * m) = L ^ 2 * Real.exp s := by
  have he : 2 * a * ((2 * m : ℕ) : ℝ) = 2 := by
    push_cast
    nlinarith [ham]
  have hes : a * s * ((2 * m : ℕ) : ℝ) = s := by
    calc
      _ = (2 * a * (m : ℝ)) * s := by push_cast; ring
      _ = s := by rw [ham, one_mul]
  rw [expandingPhysicalAmplitude_norm a b L s hL, mul_pow,
    ← Real.rpow_natCast, ← Real.rpow_mul hL.le, he, Real.rpow_two,
    ← Real.exp_nat_mul]
  congr 2
  simpa only [mul_comm] using hes

theorem expandingPhysicalAmplitude_clock (a b L s : ℝ) (hL : 0 < L)
    (m : ℕ) (ham : 2 * a * m = 1) :
    (L ^ (-2 : ℝ) * Real.exp (-s)) *
      ‖expandingPhysicalAmplitude a b L s‖ ^ (2 * m) = 1 := by
  rw [expandingPhysicalAmplitude_power a b L s hL m ham]
  have hLp : L ^ (-2 : ℝ) * L ^ 2 = 1 := by
    rw [← Real.rpow_two, ← Real.rpow_add hL]
    norm_num
  have he : Real.exp (-s) * Real.exp s = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    _ = (L ^ (-2 : ℝ) * L ^ 2) * (Real.exp (-s) * Real.exp s) := by ring
    _ = 1 := by rw [hLp, he, one_mul]

end DefocusingNLS

end OAI
