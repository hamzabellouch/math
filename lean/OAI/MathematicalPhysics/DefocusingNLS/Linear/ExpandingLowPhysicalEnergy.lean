import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingMassDerivativeEnergy

namespace OAI

/-! # The exact physical Fourier weight of the lower energy component -/

namespace DefocusingNLS

theorem expandingNorm_coordinate_physical (a L : ℝ) (N : ℕ) (hL : 1 ≤ L)
    (f : FourierL2) (n : frequencyLattice) :
    ‖f n‖ ^ 2 = (2 * Real.pi * L) ^ 12 *
      ((L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2) ^ (6 - a) + (‖n‖ / L) ^ (2 * N)) *
        ‖expandingFourierCoefficient a N L f n‖ ^ 2 := by
  have hw : expandingSobolevWeight a N L n ^ 2 = (2 * Real.pi * L) ^ 12 *
      ((L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2) ^ (6 - a) + (‖n‖ / L) ^ (2 * N)) := by
    rw [expandingSobolevWeight_sq a N L hL, ← expandingSobolevWeightSq_original a N L hL]
    congr 2
    rw [show (2 : ℝ) * (N : ℝ) = ((2 * N : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast]
  have hf := congrArg (fun z : ℂ => ‖z‖ ^ 2) (weight_mul_expandingFourierCoefficient a N L hL f n)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow] at hf
  rw [← hf, hw]

theorem expandingEnergy_coordinate_split (a L : ℝ) (N : ℕ) (hL : 1 ≤ L)
    (f : FourierL2) (n : frequencyLattice) :
    ‖expandingLowEnergy a N L hL f n‖ ^ 2 +
      (∑ j : Fin N → Fin 12, ‖expandingOrderedFourierEnergy a L N hL j f n‖ ^ 2) = ‖f n‖ ^ 2 := by
  have hlo : ‖expandingLowEnergy a N L hL f n‖ ^ 2 =
      expandingLowFraction a N L n * ‖f n‖ ^ 2 := by
    rw [expandingLowEnergy, fourierEnergyComponent_apply, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (expandingLowFraction_bounds a N L hL n).1]
  have hhi : (∑ j : Fin N → Fin 12, ‖expandingOrderedFourierEnergy a L N hL j f n‖ ^ 2) =
      (1 - expandingLowFraction a N L n) * ‖f n‖ ^ 2 := by
    simp only [expandingOrderedFourierEnergy_apply, norm_mul, mul_pow]
    rw [← Finset.sum_mul, expandingOrderedMultiplier_sq_sum a L N hL n]
  rw [hlo, hhi]
  ring

theorem expandingLowEnergy_coordinate_physical (a L : ℝ) (N : ℕ) (hL : 1 ≤ L)
    (f : FourierL2) (n : frequencyLattice) :
    ‖expandingLowEnergy a N L hL f n‖ ^ 2 = (2 * Real.pi * L) ^ 12 *
      (L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2) ^ (6 - a) *
        ‖expandingFourierCoefficient a N L f n‖ ^ 2 := by
  have he := expandingEnergy_coordinate_split a L N hL f n
  rw [expandingOrderedFourierEnergy_coordinate_sq_sum a L N hL f n,
    expandingNorm_coordinate_physical a L N hL f n] at he
  nlinarith

end DefocusingNLS

end OAI
