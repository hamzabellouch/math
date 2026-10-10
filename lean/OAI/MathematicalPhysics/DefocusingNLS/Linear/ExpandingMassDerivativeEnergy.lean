import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLowerWeightBound

namespace OAI

/-! # The exact expanding norm is controlled by physical mass and top derivatives -/

open scoped ENNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingPhysicalMassVector_coordinate_sq (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (f : FourierL2) (n : frequencyLattice) :
    ‖expandingPhysicalMassVector a k L ha ha1 hk hL f n‖ ^ 2 =
      (2 * Real.pi * L) ^ 12 * ‖expandingFourierCoefficient a k L f n‖ ^ 2 := by
  rw [expandingPhysicalMassVector_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← pow_mul]

theorem expandingOrderedFourierEnergy_coordinate_sq_sum (a L : ℝ) (N : ℕ)
    (hL : 1 ≤ L) (f : FourierL2) (n : frequencyLattice) :
    (∑ j : Fin N → Fin 12, ‖expandingOrderedFourierEnergy a L N hL j f n‖ ^ 2) =
      (2 * Real.pi * L) ^ 12 * (‖n‖ / L) ^ (2 * N) *
        ‖expandingFourierCoefficient a N L f n‖ ^ 2 := by
  have hn : ‖L⁻¹ • (n : E)‖ = ‖n‖ / L := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < L⁻¹), Submodule.norm_coe]
    ring
  have he (j : Fin N → Fin 12) : ‖expandingOrderedFourierEnergy a L N hL j f n‖ ^ 2 =
      (2 * Real.pi * L) ^ 12 * ‖homogeneousOrderedSymbol N j (L⁻¹ • (n : E))‖ ^ 2 *
        ‖expandingFourierCoefficient a N L f n‖ ^ 2 := by
    rw [expandingOrderedFourierEnergy_physical]
    simp only [norm_mul, mul_pow, Complex.norm_ofNat, Complex.norm_real, Complex.norm_pow,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos (show 0 < L by linarith)]
    ring
  simp_rw [he]
  rw [← Finset.sum_mul, ← Finset.mul_sum, homogeneousOrderedSymbol_sq_sum, hn]

theorem expandingMassDerivative_coordinate_bound (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (f : FourierL2) (n : frequencyLattice) :
    ‖f n‖ ^ 2 ≤ ((2 : ℝ) ^ N + 1) *
      (‖expandingPhysicalMassVector a N L ha ha1 hN hL f n‖ ^ 2 +
        ∑ j : Fin N → Fin 12, ‖expandingOrderedFourierEnergy a L N hL j f n‖ ^ 2) := by
  have hw : expandingSobolevWeight a N L n ^ 2 = (2 * Real.pi * L) ^ 12 *
      ((L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2) ^ (6 - a) + (‖n‖ / L) ^ (2 * N)) := by
    rw [expandingSobolevWeight_sq a N L hL, ← expandingSobolevWeightSq_original a N L hL]
    congr 2
    rw [show (2 : ℝ) * (N : ℝ) = ((2 * N : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast]
  have hf := congrArg (fun z : ℂ => ‖z‖ ^ 2) (weight_mul_expandingFourierCoefficient a N L hL f n)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow] at hf
  rw [← hf, hw, expandingPhysicalMassVector_coordinate_sq,
    expandingOrderedFourierEnergy_coordinate_sq_sum]
  have hlo := expandingLowerWeight_le_mass_top a L N ha ha1 hN hL n
  have hweight : (L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2) ^ (6 - a) + (‖n‖ / L) ^ (2 * N) ≤
      ((2 : ℝ) ^ N + 1) * (1 + (‖n‖ / L) ^ (2 * N)) := by nlinarith
  calc
    _ ≤ (2 * Real.pi * L) ^ 12 * (((2 : ℝ) ^ N + 1) * (1 + (‖n‖ / L) ^ (2 * N))) *
        ‖expandingFourierCoefficient a N L f n‖ ^ 2 := by gcongr
    _ = _ := by ring

end DefocusingNLS

end OAI
