import OAI.NumberTheory.Ostmann.Arithmetic.PeriodicWeightPoisson
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGaussMultiplier

namespace OAI

/-! # The first Poisson formula for the actual primitive Jacobi character -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform

theorem quadratic_primitive_poisson {q : ℕ} [NeZero q]
    (hq : Squarefree q) (ho : Odd q) (ψ : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) :
    (∑' n : ℤ, (jacobiSym n q : ℂ) * ψ ((n : ℝ) / X)) =
      (X : ℂ) / q * gaussSum (jacobiComplex q) ZMod.stdAddChar *
        ∑' h : ℤ, (jacobiSym h q : ℂ) * 𝓕 ψ ((h : ℝ) * X / q) := by
  have hp := scaled_periodic_poisson (jacobiComplex q) ψ X hX
  simp_rw [jacobiComplex_intCast] at hp
  rw [hp]
  simp_rw [primitive_character_fourier _ (jacobiComplex_squarefree_primitive q hq ho),
    (jacobiComplex_isQuadratic q).inv, neg_neg, jacobiComplex_intCast]
  rw [← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

theorem quadratic_primitive_poisson_normalized {q : ℕ} [NeZero q]
    (hq : Squarefree q) (ho : Odd q) (ψ : 𝓢(ℝ, ℂ)) {X : ℝ} (hX : 0 < X) :
    (∑' n : ℤ, (jacobiSym n q : ℂ) * ψ ((n : ℝ) / X)) =
      quadraticGaussMultiplier q * ((X / Real.sqrt q : ℝ) : ℂ) *
        ∑' h : ℤ, (jacobiSym h q : ℂ) * 𝓕 ψ ((h : ℝ) * X / q) := by
  rw [quadratic_primitive_poisson hq ho ψ hX]
  congr 1
  rw [quadraticGaussMultiplier, dite_eq_right (NeZero.ne q), jacobiGaussPhase,
    Complex.ofReal_div]
  have hs : (Real.sqrt (q : ℝ) : ℂ) ^ 2 = q := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg q)
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hsC : (Real.sqrt (q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < q by exact_mod_cast NeZero.pos q)).ne'
  field_simp
  linear_combination (X : ℂ) * gaussSum (jacobiComplex q) ZMod.stdAddChar * hs

end Ostmann

end OAI
