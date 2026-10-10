import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingOrderedEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalFourier

namespace OAI

/-! # Ordered torus energy in the physical frequency convention -/

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousOrderedSymbol_smul (N : ℕ) (j : Fin N → Fin 12) (c : ℝ) (ξ : E) :
    homogeneousOrderedSymbol N j (c • ξ) = (c : ℂ) ^ N * homogeneousOrderedSymbol N j ξ := by
  unfold homogeneousOrderedSymbol
  simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  simp_rw [mul_assoc]
  rw [Finset.prod_mul_distrib]
  simp

theorem expandingOrderedPhysical_scale (L : ℝ) (hL : 0 < L) (N : ℕ) :
    (2 * Real.pi * L) ^ 6 * (L⁻¹) ^ N = (2 * Real.pi) ^ 6 * L ^ (6 - (N : ℝ)) := by
  have hp : L ^ (6 - (N : ℝ)) = L ^ (6 : ℕ) * (L⁻¹) ^ N := by
    rw [Real.rpow_sub hL]
    simp only [Real.rpow_natCast, div_eq_mul_inv, inv_pow]
    rw [Real.rpow_ofNat]
  rw [hp, mul_pow]
  ring

theorem expandingOrderedFourierEnergy_physical (a L : ℝ) (N : ℕ) (hL : 1 ≤ L)
    (j : Fin N → Fin 12) (f : FourierL2) (n : frequencyLattice) :
    expandingOrderedFourierEnergy a L N hL j f n =
      ((2 * Real.pi * L) ^ 6 : ℂ) * homogeneousOrderedSymbol N j (L⁻¹ • (n : E)) *
        expandingFourierCoefficient a N L f n := by
  rw [expandingOrderedFourierEnergy_apply, homogeneousOrderedSymbol_smul]
  have hp := congrArg Complex.ofReal (expandingOrderedPhysical_scale L (by linarith) N)
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv] at hp
  unfold expandingOrderedMultiplier expandingFourierCoefficient
  push_cast at hp ⊢
  linear_combination -(homogeneousOrderedSymbol N j n *
    (expandingSobolevWeight a N L n : ℂ)⁻¹ * f n) * hp

end DefocusingNLS

end OAI
