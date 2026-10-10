import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLowPhysicalEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.LowWeightInterpolation

namespace OAI

/-! # Uniform lower-energy interpolation on every expanding torus -/

open scoped ENNReal

namespace DefocusingNLS

theorem expandingLowEnergy_interpolation (a ε : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L) (f : FourierL2),
      ‖expandingLowEnergy a N L hL f‖ ^ 2 ≤ ε * ‖f‖ ^ 2 +
        C * ‖expandingPhysicalMassVector a N L ha ha1 hN hL f‖ ^ 2 := by
  obtain ⟨C, hC, hc⟩ := lowBesselWeight_interpolation a N ε ha ha1 hN hε
  refine ⟨C, hC, ?_⟩
  intro L hL f
  have hcoord (n : frequencyLattice) : ‖expandingLowEnergy a N L hL f n‖ ^ 2 ≤
      ε * ‖f n‖ ^ 2 + C * ‖expandingPhysicalMassVector a N L ha ha1 hN hL f n‖ ^ 2 := by
    have hw := hc (L ^ (-2 : ℝ)) (‖n‖ / L) (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num))
      (div_nonneg (norm_nonneg _) (by linarith))
    rw [show (2 : ℝ) * (N : ℝ) = ((2 * N : ℕ) : ℝ) by push_cast; rfl,
      Real.rpow_natCast] at hw
    rw [expandingLowEnergy_coordinate_physical a L N hL f n,
      expandingNorm_coordinate_physical a L N hL f n,
      expandingPhysicalMassVector_coordinate_sq a N L ha ha1 hN hL f n]
    have hA : 0 ≤ (L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2) ^ (6 - a) := by positivity
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw
      (show 0 ≤ (2 * Real.pi * L) ^ 12 by positivity))
      (sq_nonneg ‖expandingFourierCoefficient a N L f n‖)
    nlinarith [mul_nonneg hε.le (mul_nonneg
      (mul_nonneg (show 0 ≤ (2 * Real.pi * L) ^ 12 by positivity) hA)
      (sq_nonneg ‖expandingFourierCoefficient a N L f n‖))]
  have hs (g : FourierL2) : HasSum (fun n : frequencyLattice => ‖g n‖ ^ 2) (‖g‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) g
  exact hasSum_le hcoord (hs _) (((hs f).mul_left ε).add
    ((hs (expandingPhysicalMassVector a N L ha ha1 hN hL f)).mul_left C))

end DefocusingNLS

end OAI
