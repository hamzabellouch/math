import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.GeomSum
import OAI.NumberTheory.Catalan.Polynomial.PalindromicCoefficientMatrices

namespace OAI


noncomputable section

namespace InternalCatalan

open Polynomial
open scoped BigOperators

theorem palindromic_one_sub_X_sq_ne_zero {p : ℕ} [Fact p.Prime] :
    (1 - X ^ 2 : (ZMod p)[X]) ≠ 0 := by
  intro h
  have hcoeff : (1 : ZMod p) = 0 := by
    simpa [coeff_sub, coeff_one, coeff_X_pow] using
      congrArg (fun P : (ZMod p)[X] => P.coeff 0) h
  exact one_ne_zero hcoeff

theorem palindromic_prime_geometric_identity {p : ℕ} [Fact p.Prime] :
    (∑ j ∈ Finset.range p, (X : (ZMod p)[X]) ^ (2 * j)) =
      (1 - X ^ 2) ^ (p - 1) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hsum : (∑ j ∈ Finset.range p, (X : (ZMod p)[X]) ^ (2 * j)) =
      ∑ j ∈ Finset.range p, ((X : (ZMod p)[X]) ^ 2) ^ j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact pow_mul (X : (ZMod p)[X]) 2 j
  apply mul_right_cancel₀ (palindromic_one_sub_X_sq_ne_zero (p := p))
  calc
    (∑ j ∈ Finset.range p, (X : (ZMod p)[X]) ^ (2 * j)) * (1 - X ^ 2) =
        1 - (X ^ 2) ^ p := by
      rw [hsum]
      exact geom_sum_mul_neg (X ^ 2 : (ZMod p)[X]) p
    _ = (1 - X ^ 2) ^ p := by rw [sub_pow_char, one_pow]
    _ = (1 - X ^ 2) ^ (p - 1) * (1 - X ^ 2) := by
      rw [← pow_succ, show p - 1 + 1 = p by omega]

end InternalCatalan

end

end OAI
