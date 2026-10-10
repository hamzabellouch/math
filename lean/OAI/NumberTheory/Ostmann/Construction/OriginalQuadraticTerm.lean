import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticQuadraticCoefficient

namespace OAI

/-! # The modular and real phases in the manuscript's original summand -/

namespace Ostmann

open scoped SchwartzMap

theorem original_quadratic_residue_argument (M s w : ℕ) (V U : Finset ℕ) :
    divisorQuadraticScalar (quadraticInverseResidue M) V U *
      (w : ZMod U.toList.prod) ^ 2 * (s : ZMod U.toList.prod) =
      -((s : ZMod U.toList.prod) * (V.toList.prod : ZMod U.toList.prod) *
        (w : ZMod U.toList.prod) ^ 2 * (M : ZMod U.toList.prod)⁻¹) := by
  unfold divisorQuadraticScalar quadraticInverseResidue
  ring

theorem original_quadratic_real_phase (h₀ θ : ℝ) (q s v w : ℕ) :
    realAdditivePhase ((h₀ + θ) * v * (w : ℝ) ^ 2 / q) ^ s =
      realAdditivePhase ((h₀ + θ) * s * v * (w : ℝ) ^ 2 / q) := by
  rw [← realAdditivePhase_nat_mul]
  congr 1
  ring

theorem original_quadratic_density_term (M s w : ℕ) (V U : Finset ℕ)
    [NeZero U.toList.prod] (g : ZMod U.toList.prod → ℂ) (h₀ θ R : ℝ)
    (Φ : 𝓢(ℝ, ℂ)) :
    quadraticDensityTerm g (divisorQuadraticScalar (quadraticInverseResidue M) V U)
      (h₀ + θ) Φ R V.toList.prod s w =
      g (-((s : ZMod U.toList.prod) * (V.toList.prod : ZMod U.toList.prod) *
          (w : ZMod U.toList.prod) ^ 2 * (M : ZMod U.toList.prod)⁻¹)) *
        realAdditivePhase ((h₀ + θ) * s * V.toList.prod * (w : ℝ) ^ 2 / U.toList.prod) *
        Φ ((s : ℝ) * V.toList.prod * (w : ℝ) ^ 2 / (R * U.toList.prod)) := by
  rw [quadraticDensityTerm, original_quadratic_residue_argument, original_quadratic_real_phase]

end Ostmann

end OAI
