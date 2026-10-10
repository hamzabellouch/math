import Mathlib
import OAI.Computability.MaxCut.Games.MatrixCharacters

namespace OAI

/-!
# Normalized Fourier analysis of finite binary linear-map spaces

The coefficient normalization is uniform expectation on the primal space. The
Parseval sum over frequencies is an unnormalized sum. The underlying complex
Fourier system is the actual trace-character family on the finite additive group.
Completeness is proved directly from character cancellation and finite sums.
-/

noncomputable section

namespace MaxCutGames.Fourier.MatrixFourier

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate
open Finset
open MaxCutGames.Fourier.MatrixCharacters

section FiniteGroup

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Uniformly normalized complex Fourier coefficient. -/
def fourierCoeff (f : G → ℂ) (ψ : AddChar G ℂ) : ℂ :=
  𝔼 x, f x * star (ψ x)

theorem fourierCoeff_sum {J : Type*} (s : Finset J) (f : J → G → ℂ)
    (ψ : AddChar G ℂ) :
    fourierCoeff (∑ j ∈ s, f j) ψ = ∑ j ∈ s, fourierCoeff (f j) ψ := by
  simp only [fourierCoeff, Finset.sum_apply, Finset.sum_mul]
  exact Finset.expect_sum_comm _ _ _

theorem fourierCoeff_smul (c : ℂ) (f : G → ℂ) (ψ : AddChar G ℂ) :
    fourierCoeff (c • f) ψ = c * fourierCoeff f ψ := by
  simp only [fourierCoeff, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact Finset.mul_expect _ _ _ |>.symm

omit [AddCommGroup G] in
theorem star_expect (f : G → ℂ) :
    star (𝔼 x, f x) = 𝔼 x, star (f x) := by
  simp [Fintype.expect_eq_sum_div_card]

theorem star_fourierCoeff (f : G → ℂ) (ψ : AddChar G ℂ) :
    star (fourierCoeff f ψ) = 𝔼 x, star (f x) * ψ x := by
  rw [fourierCoeff, star_expect]
  simp [star_mul, mul_comm]

end FiniteGroup

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

/-- Real coefficient on the actual space of binary linear maps. -/
def linearCoeff (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) : ℝ :=
  𝔼 X, f X * (linearTraceCharacter S X).re

theorem card_linearMap_reverse :
    Fintype.card (F →ₗ[F2] E) = Fintype.card (E →ₗ[F2] F) := by
  classical
  let bE := Module.finBasis F2 E
  let bF := Module.finBasis F2 F
  calc
    Fintype.card (F →ₗ[F2] E) =
        Fintype.card (Matrix (Fin (Module.finrank F2 E))
          (Fin (Module.finrank F2 F)) F2) :=
      Fintype.card_congr (LinearMap.toMatrix bF bE).toEquiv
    _ = Fintype.card (Matrix (Fin (Module.finrank F2 F))
          (Fin (Module.finrank F2 E)) F2) := by
      exact Fintype.card_congr
        { toFun := Matrix.transpose
          invFun := Matrix.transpose
          left_inv := Matrix.transpose_transpose
          right_inv := Matrix.transpose_transpose }
    _ = Fintype.card (E →ₗ[F2] F) :=
      (Fintype.card_congr (LinearMap.toMatrix bE bF).toEquiv).symm

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem linearTraceCharacter_star (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    star (linearTraceCharacter S X) = linearTraceCharacter S X := by
  calc
    _ = star (((linearTraceCharacter S X).re : ℝ) : ℂ) :=
      congrArg star (linearTraceCharacter_real S X).symm
    _ = ((linearTraceCharacter S X).re : ℂ) := by simp
    _ = linearTraceCharacter S X := linearTraceCharacter_real S X

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem linearMap_add_eq_zero_iff (X Y : E →ₗ[F2] F) :
    X + Y = 0 ↔ X = Y := by
  have htwo : (1 + 1 : F2) = 0 := by decide
  have hself : Y + Y = 0 := by
    have h := congrArg (fun c : F2 => c • Y) htwo
    simpa only [add_smul, one_smul, zero_smul] using h
  have hneg : -Y = Y := neg_eq_iff_add_eq_zero.mpr hself
  rw [add_eq_zero_iff_eq_neg, hneg]

/-- Exact trace-character orthogonality with the frequency sum unnormalized. -/
theorem linear_character_kernel (X Y : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, star (linearTraceCharacter S X) * linearTraceCharacter S Y =
      if X = Y then (Fintype.card (E →ₗ[F2] F) : ℂ) else 0 := by
  classical
  calc
    _ = ∑ S : F →ₗ[F2] E, linearTraceCharacter S (X + Y) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [linearTraceCharacter_star, AddChar.map_add_eq_mul]
    _ = ∑ S : F →ₗ[F2] E, linearTraceCharacter (X + Y) S := by
      apply Finset.sum_congr rfl
      intro S _
      exact linearTraceCharacter_swap S (X + Y)
    _ = if X + Y = 0 then (Fintype.card (F →ₗ[F2] E) : ℂ) else 0 :=
      sum_linearTraceCharacter (X + Y)
    _ = _ := by rw [linearMap_add_eq_zero_iff, card_linearMap_reverse]

omit [Fintype (F →ₗ[F2] E)] in
theorem linear_complexCoeff_character (S T : F →ₗ[F2] E) :
    fourierCoeff (linearTraceCharacter S : (E →ₗ[F2] F) → ℂ)
      (linearTraceCharacter T) = if T = S then 1 else 0 := by
  classical
  simp only [fourierCoeff, linearTraceCharacter_star, ← AddChar.add_apply,
    ← linearTraceCharacter_add, Fintype.expect_eq_sum_div_card,
    sum_linearTraceCharacter, linearMap_add_eq_zero_iff]
  by_cases h : S = T
  · subst T
    simp
  · simp [h, Ne.symm h]

/-- Fourier inversion obtained directly from the finite trace orthogonality sum. -/
theorem linear_complex_inversion (f : (E →ₗ[F2] F) → ℂ) (Y : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, fourierCoeff f (linearTraceCharacter S) *
      linearTraceCharacter S Y = f Y := by
  classical
  simp only [fourierCoeff]
  simp_rw [Finset.expect_mul, mul_assoc]
  rw [← Finset.expect_sum_comm]
  simp_rw [← Finset.mul_sum, linear_character_kernel]
  rw [Finset.expect_eq_sum_div_card]
  simp [mul_ite]

/-- Mixed Parseval with normalized primal expectation and unnormalized frequency sum. -/
theorem linear_complex_parseval (f g : (E →ₗ[F2] F) → ℂ) :
    ∑ S : F →ₗ[F2] E, star (fourierCoeff f (linearTraceCharacter S)) *
      fourierCoeff g (linearTraceCharacter S) = 𝔼 X, star (f X) * g X := by
  simp_rw [star_fourierCoeff, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro X _
  calc
    (∑ S : F →ₗ[F2] E, (star (f X) * linearTraceCharacter S X) *
        fourierCoeff g (linearTraceCharacter S)) =
        star (f X) * ∑ S : F →ₗ[F2] E,
          fourierCoeff g (linearTraceCharacter S) * linearTraceCharacter S X := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ac_rfl
    _ = star (f X) * g X := by rw [linear_complex_inversion]

theorem complex_ofReal_expect {J : Type*} [Fintype J] (f : J → ℝ) :
    ((𝔼 j, f j : ℝ) : ℂ) = 𝔼 j, (f j : ℂ) := by
  simp only [Fintype.expect_eq_sum_div_card, Complex.ofReal_div, Complex.ofReal_natCast]
  congr 1
  exact map_sum Complex.ofRealHom f Finset.univ

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_complex (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    (linearCoeff f S : ℂ) =
      fourierCoeff (fun X => (f X : ℂ)) (linearTraceCharacter S) := by
  rw [linearCoeff, complex_ofReal_expect, fourierCoeff]
  apply Finset.expect_congr rfl
  intro X _
  rw [Complex.ofReal_mul, linearTraceCharacter_real, linearTraceCharacter_star]

/-- Parseval for real functions and the real binary trace coefficients. -/
theorem linear_parseval_inner (f g : (E →ₗ[F2] F) → ℝ) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S =
      𝔼 X, f X * g X := by
  apply Complex.ofReal_injective
  calc
    ((∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S : ℝ) : ℂ) =
        ∑ S : F →ₗ[F2] E,
          star (fourierCoeff (fun X => (f X : ℂ)) (linearTraceCharacter S)) *
            fourierCoeff (fun X => (g X : ℂ)) (linearTraceCharacter S) := by
      change Complex.ofRealHom (∑ S : F →ₗ[F2] E, linearCoeff f S * linearCoeff g S) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [← linearCoeff_complex, ← linearCoeff_complex]
      simp
    _ = 𝔼 X, star (f X : ℂ) * (g X : ℂ) := linear_complex_parseval _ _
    _ = ((𝔼 X, f X * g X : ℝ) : ℂ) := by
      rw [complex_ofReal_expect]
      simp

theorem linear_parseval (f : (E →ₗ[F2] F) → ℝ) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S ^ 2 = 𝔼 X, f X ^ 2 := by
  simpa only [pow_two] using linear_parseval_inner f f

theorem linear_fourier_inversion (f : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    ∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re = f X := by
  apply Complex.ofReal_injective
  calc
    ((∑ S : F →ₗ[F2] E, linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) =
        ∑ S : F →ₗ[F2] E,
          fourierCoeff (fun Y => (f Y : ℂ)) (linearTraceCharacter S) *
            linearTraceCharacter S X := by
      change Complex.ofRealHom (∑ S : F →ₗ[F2] E,
        linearCoeff f S * (linearTraceCharacter S X).re) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro S _
      change ((linearCoeff f S * (linearTraceCharacter S X).re : ℝ) : ℂ) = _
      rw [Complex.ofReal_mul, linearCoeff_complex, linearTraceCharacter_real]
    _ = (f X : ℂ) := linear_complex_inversion _ X

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_sum {J : Type*} (s : Finset J)
    (f : J → (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (∑ j ∈ s, f j) S = ∑ j ∈ s, linearCoeff (f j) S := by
  simp only [linearCoeff, Finset.sum_apply, Finset.sum_mul]
  exact Finset.expect_sum_comm _ _ _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_smul (c : ℝ) (f : (E →ₗ[F2] F) → ℝ) (S : F →ₗ[F2] E) :
    linearCoeff (c • f) S = c * linearCoeff f S := by
  simp only [linearCoeff, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact Finset.mul_expect _ _ _ |>.symm

omit [Fintype (F →ₗ[F2] E)] in
theorem linearCoeff_character (S T : F →ₗ[F2] E) :
    linearCoeff (fun X => (linearTraceCharacter S X).re) T =
      if T = S then 1 else 0 := by
  classical
  apply Complex.ofReal_injective
  rw [linearCoeff_complex]
  simp only [linearTraceCharacter_real, linear_complexCoeff_character]
  split_ifs <;> simp

end MaxCutGames.Fourier.MatrixFourier
end

end OAI
