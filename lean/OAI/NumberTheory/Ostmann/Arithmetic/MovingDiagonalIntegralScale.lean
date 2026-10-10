import OAI.NumberTheory.Ostmann.Arithmetic.MovingDiagonalOuterWeight
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternCoefficientMass

namespace OAI

/-! # Removing the harmless constant normalization of the diagonal multiplier -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem movingDiagonalOuterWeight_denormalize {A σ J : Type*} [Fintype J]
    (prime : A → ℕ) (reg : J → σ) (active : J → Bool)
    (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (diagonal : Bool)
    (u v : ℝ) (x : σ → A) :
    (diagonalOuterMajorant B D diagonal : ℂ) *
      movingDiagonalOuterWeight prime reg active φ Jleft Jright B D diagonal u v x =
      giantOuterWeight φ Jleft Jright diagonal (Real.exp u) (Real.exp v) *
        (inactiveRegularDensity prime reg active x : ℂ) := by
  unfold movingDiagonalOuterWeight
  have hc : (diagonalOuterMajorant B D diagonal : ℂ) ≠ 0 := by
    exact_mod_cast (diagonalOuterMajorant_pos B D diagonal).ne'
  exact mul_div_cancel₀ _ hc

/-- The normalized multiplier costs only its fixed outer majorant after both
integrals and the original signed pattern average. -/
theorem movingPattern_diagonal_integral_norm {A B C J : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype J] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (pattern : Bool × MovingSampleIndex n → C)
    (reg : J → Fin (N + 1)) (active : J → Bool)
    (φ : ℝ → ℝ) (Jleft Jright Bφ Dφ : ℝ) (diagonal : Bool)
    (raw : ℝ → ℝ → (Fin (N + 1) → A) → ℂ)
    (haar : (Fin (N + 1) → A) → ℂ) (u v a b center bound : ℝ)
    (hbound : ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern
      (fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
        (movingDiagonalOuterWeight prime reg active φ Jleft Jright Bφ Dφ diagonal z y x *
          raw z y x) * (Real.exp (z - center) : ℂ) / (y : ℂ)) x * haar x‖ ≤ bound) :
    ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern
      (fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
        ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) *
          (inactiveRegularDensity prime reg active x : ℂ)) * raw z y x) *
            (Real.exp (z - center) : ℂ) / (y : ℂ)) x * haar x‖ ≤
      diagonalOuterMajorant Bφ Dφ diagonal * bound := by
  let K := diagonalOuterMajorant Bφ Dφ diagonal
  have hK : 0 ≤ K := (diagonalOuterMajorant_pos Bφ Dφ diagonal).le
  have he (x) :
      (∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
        ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) *
          (inactiveRegularDensity prime reg active x : ℂ)) * raw z y x) *
            (Real.exp (z - center) : ℂ) / (y : ℂ)) =
      (K : ℂ) * (∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
        (movingDiagonalOuterWeight prime reg active φ Jleft Jright Bφ Dφ diagonal z y x *
          raw z y x) * (Real.exp (z - center) : ℂ) / (y : ℂ)) := by
    rw [← integral_const_mul]
    congr 1
    funext z
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [← movingDiagonalOuterWeight_denormalize prime reg active φ Jleft Jright Bφ Dφ diagonal z y x]
    change (((K : ℂ) * _) * _) * _ / _ = _
    ring
  let original := fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
    ((giantOuterWeight φ Jleft Jright diagonal (Real.exp z) (Real.exp y) *
      (inactiveRegularDensity prime reg active x : ℂ)) * raw z y x) *
        (Real.exp (z - center) : ℂ) / (y : ℂ)
  let normalized := fun x => ∫ z in Set.Ioc u v, ∫ y in Set.Ioc a b,
    (movingDiagonalOuterWeight prime reg active φ Jleft Jright Bφ Dφ diagonal z y x *
      raw z y x) * (Real.exp (z - center) : ℂ) / (y : ℂ)
  change ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern original x * haar x‖ ≤ _
  change ‖∑ x, movingOriginalPatternWeight e μ ν prime n pattern normalized x * haar x‖ ≤ bound at hbound
  have hsum : (∑ x, movingOriginalPatternWeight e μ ν prime n pattern original x * haar x) =
      (K : ℂ) * ∑ x, movingOriginalPatternWeight e μ ν prime n pattern normalized x * haar x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    conv_lhs => rw [movingOriginalPatternWeight_eq_coefficient_mul]
    conv_rhs => rw [movingOriginalPatternWeight_eq_coefficient_mul]
    change _ * (original x) * _ = _ * (_ * normalized x * _)
    have hi : original x = (K : ℂ) * normalized x := he x
    rw [hi]
    ring
  rw [hsum, norm_mul, Complex.norm_real, Real.norm_of_nonneg hK]
  exact mul_le_mul_of_nonneg_left hbound hK

end Ostmann

end OAI
