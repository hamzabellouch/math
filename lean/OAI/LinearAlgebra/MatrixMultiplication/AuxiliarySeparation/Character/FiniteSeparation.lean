import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.Basic
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Degeneration
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Dot
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.CharacterBounds

namespace OAI

/-!
# The character bound from finite separation

The explicit Fourier and square-weight construction gives a polynomial tensor
whose nonzero evaluations restrict from exactly `5M` complete source copies.
Character monotonicity follows by interpolation and tensor powering; it does
not require continuity of the character.
-/

noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

variable {M : ℕ} {X Y Z : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype Z] in
private theorem polynomial_rank_bound
    (P : Tensor (Polynomial ℂ) X Y Z) :
    Tensor.RankAtMost P (Fintype.card (X × Y)) := by
  classical
  let a : X × Y → X → Polynomial ℂ := fun i x => if i.1 = x then 1 else 0
  let b : X × Y → Y → Polynomial ℂ := fun i y => if i.2 = y then 1 else 0
  let c : X × Y → Z → Polynomial ℂ := fun i z => P i.1 i.2 z
  have heq : P = fun x y z => ∑ i, Tensor.rankOne (a i) (b i) (c i) x y z := by
    funext x y z
    simp [Tensor.rankOne, a, b, c, Fintype.sum_prod_type, ite_mul, mul_ite]
  rw [heq]
  exact Tensor.rankAtMost_sum_rankOne a b c

/-- The explicit separation polynomial, viewed as a polynomial approximation
to its constant tensor. Its rank bound is supplied by a coordinate expansion. -/
def separationPolynomialApproximation {ζ : ℂ} (hM : 0 < M)
    (hζ : IsPrimitiveRoot ζ (5 * M)) (B : Fin M → Tensor ℂ X Y Z) :
    Tensor.PolynomialApproximation (separationTarget B)
      (Fintype.card ((X × Fin M) × ((Fin M × Y) × Fin M))) 0 ((M - 1) ^ 2) where
  polynomial := separationPolynomial ζ B
  rank_bound := polynomial_rank_bound _
  vanishes := by
    intro _ _ _ k hk
    exact (Nat.not_lt_zero k hk).elim
  leading := by
    intro x y z
    exact congrFun (congrFun (congrFun (separationPolynomial_coeff_zero hM hζ B) x) y) z
  degree_bound := separationPolynomial_degree hM hζ B

namespace Character

variable (χ : Character)

/-- The separated constant tensor costs at most the character of the `5M`
source copies. This uses the explicit polynomial, not topological continuity. -/
theorem value_separationTarget_le (hM : 0 < M) (B : Fin M → Tensor ℂ X Y Z) :
    χ.value (separationTarget B) ≤
      5 * (M : ℝ) * χ.value (sharedFirstTensor B) := by
  classical
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (5 * M : ℕ))
  have hζ : IsPrimitiveRoot ζ (5 * M) :=
    Complex.isPrimitiveRoot_exp _ (by omega)
  have hbound : χ.value (separationTarget B) ≤
      χ.value (Tensor.directSum (fun _ : Fin (5 * M) => sharedFirstTensor B)) := by
    apply χ.value_le_of_polynomialApproximation
      (separationPolynomialApproximation hM hζ B) (χ.nonneg _)
    intro t ht
    change χ.value (fun x y z => (separationPolynomial ζ B x y z).eval t) ≤ _
    rw [separationPolynomial_eval hM hζ B t ht]
    exact χ.monotone _ _ _ _
  simpa only [χ.value_copies, Nat.cast_mul, Nat.cast_ofNat] using hbound

/-- Character accounting for the genuine direct sum in the separated tensor. -/
theorem value_separationTarget (hM : 0 < M) (B : Fin M → Tensor ℂ X Y Z) :
    χ.value (separationTarget B) =
      (∑ h, χ.value (B h)) * (M : ℝ) ^ χ.pX := by
  classical
  rw [separationTarget_eq_directSum, χ.value_reindex, χ.map_directSum]
  simp only [χ.map_product, χ.value_cyclic_cyclic_dotPairing hM, Finset.sum_mul]

/-- Exact finite character separation: the common first coordinate can be
separated at a cost of `5M`, retaining an `M`-dimensional first-leg dot factor. -/
theorem finiteSeparation_bound (hM : 0 < M) (B : Fin M → Tensor ℂ X Y Z) :
    (∑ h, χ.value (B h)) * (M : ℝ) ^ χ.pX ≤
      5 * (M : ℝ) * χ.value (sharedFirstTensor B) := by
  rw [← χ.value_separationTarget hM B]
  exact χ.value_separationTarget_le hM B

end Character
end MatrixMultiplication.AuxiliarySeparation

end

end OAI
