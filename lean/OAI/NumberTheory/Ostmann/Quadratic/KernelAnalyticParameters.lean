import OAI.NumberTheory.Ostmann.QuadraticCenter.AllKernelSplitMass

namespace OAI

/-! # Concrete error absorption for the quadratic-kernel parameters -/

namespace Ostmann

/-- Choose the kernel-size exponent after the absolute zero-comparison
constant has been fixed. -/
theorem exists_kernel_size_exponent (Cz : ℝ) (hCz : 5 ≤ Cz) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 1000 ∧ 4 * Cz * η = 1 / 40000 := by
  have hp : 0 < Cz := by linarith
  refine ⟨1 / (160000 * Cz), by positivity, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < 160000 * Cz)).mpr
    nlinarith
  · field_simp
    ring

theorem kernel_sqrt_error_absorption (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hsize : (40000 * K) ^ 2 ≤ L) : K * Real.sqrt L ≤ L / 40000 := by
  have hroot : 40000 * K ≤ Real.sqrt L := (Real.le_sqrt (by positivity) hL).mpr hsize
  have hh := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg L)
  rw [Real.mul_self_sqrt hL] at hh
  nlinarith

/-- The Page threshold is (log X)^100 and Siegel is used only at exponent
1/200, giving a square-root error in log X. -/
theorem page_threshold_siegel_power (L : ℝ) (hL : 0 ≤ L) :
    ((L ^ (100 : ℕ)) : ℝ) ^ (1 / 200 : ℝ) = Real.sqrt L := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
  norm_num
  rw [Real.sqrt_eq_rpow]

/-- The logarithmic conductor cost and square-root Siegel cost are both
absorbed by the chosen fixed coefficient of L. -/
theorem kernel_zero_error_absorption (Cz η K A H L logQ : ℝ)
    (hCz : 0 ≤ Cz) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hη : 4 * Cz * η ≤ 1 / 40000)
    (hQ : logQ ≤ 2 * η * L + Real.log 20)
    (hKsize : (40000 * K) ^ 2 ≤ L)
    (hconst : 40000 * (2 * Cz * Real.log 20 + H + A + 2) ≤ L) :
    2 * Cz * logQ + K * Real.sqrt L + H + A + 2 ≤ L / 10000 := by
  have hq := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 2 * Cz by positivity)
  have heta := mul_le_mul_of_nonneg_right hη hL
  have hsqrt := kernel_sqrt_error_absorption K L hK hL hKsize
  nlinarith

/-- The elementary divisor bound is o(L) with a square-root cutoff. -/
theorem kernel_divisor_error_absorption (D Y : ℕ) (L : ℝ)
    (hL : 0 < L) (hlarge : (40000 : ℝ) ^ 2 ≤ L)
    (hYlo : Real.sqrt L ≤ Y) (hYhi : (Y : ℝ) ≤ Real.sqrt L + 1)
    (hlogD : Real.log D ≤ L) :
    (Y : ℝ) + Real.log D / Y ≤ L / 10000 := by
  have hr : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hY : (0 : ℝ) < Y := hr.trans_le hYlo
  have hroot : 40000 ≤ Real.sqrt L := (Real.le_sqrt (by norm_num) hL.le).mpr hlarge
  have hsquare : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL.le
  have hdiv : Real.log D / Y ≤ Real.sqrt L := by
    apply (div_le_iff₀ hY).mpr
    calc
      Real.log D ≤ L := hlogD
      _ = Real.sqrt L * Real.sqrt L := hsquare.symm
      _ ≤ Real.sqrt L * Y := mul_le_mul_of_nonneg_left hYlo hr.le
  have hprod := mul_le_mul_of_nonneg_right hroot hr.le
  rw [hsquare] at hprod
  nlinarith

end Ostmann

end OAI
