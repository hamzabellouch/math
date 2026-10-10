import Mathlib.Algebra.Field.ZMod
import OAI.NumberTheory.Catalan.FiniteMatrices.FixedDeterminantsNonzero

namespace OAI

section

noncomputable section
namespace InternalCatalan

local instance : Fact (Nat.Prime 101) := ⟨by decide +kernel⟩

def fixedGaussianDenominator : ℤ :=
  854041599922236190937524347070927377276592590715779683450880000

theorem fixedGaussianDenominator_rat_ne_zero :
    (fixedGaussianDenominator : ℚ) ≠ 0 := by
  decide +kernel

theorem fixedGaussianDenominator_mod :
    (fixedGaussianDenominator : ZMod 101) = 62 := by
  decide +kernel

theorem fixedGaussianDenominator_mod_ne_zero :
    (fixedGaussianDenominator : ZMod 101) ≠ 0 := by
  decide +kernel

theorem fixedGaussianDenominator_mod_inv :
    (fixedGaussianDenominator : ZMod 101)⁻¹ = 44 := by
  decide +kernel

theorem fixedMatrix_eq_gaussian_fraction (sigma : ℤ) (r k : Fin 48) :
    fixedMatrix (sigma : ℚ) r k =
      (fixedIntegerMatrix fixedIntegerBaseCanonical sigma r k : ℚ) /
        (fixedGaussianDenominator : ℚ) := by
  have h := congrArg (fun M : Matrix (Fin 48) (Fin 48) ℚ => M r k)
    (fixedCanonicalMatrix_integer_lift sigma)
  change (fixedIntegerMatrix fixedIntegerBaseCanonical sigma r k : ℚ) =
    (fixedGaussianDenominator : ℚ) * fixedMatrix (sigma : ℚ) r k at h
  apply (eq_div_iff fixedGaussianDenominator_rat_ne_zero).2
  simpa only [mul_comm] using h.symm

def fixedGaussianUnscaled (sigma : ℤ) : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  fun r k => (fixedIntegerMatrix fixedIntegerBaseCanonical sigma r k : ZMod 101) /
    (fixedGaussianDenominator : ZMod 101)

theorem fixedGaussianUnscaled_zero :
    fixedGaussianUnscaled 0 = (44 : ZMod 101) • fixedLiteralModZero := by
  ext r k
  have h := congrArg (fun M : Matrix (Fin 48) (Fin 48) (ZMod 101) => M r k)
    fixedCanonicalMatrix_zero_mod
  change (fixedIntegerMatrix fixedIntegerBaseCanonical 0 r k : ZMod 101) =
    fixedLiteralModZero r k at h
  change (fixedIntegerMatrix fixedIntegerBaseCanonical 0 r k : ZMod 101) /
    (fixedGaussianDenominator : ZMod 101) = 44 * fixedLiteralModZero r k
  rw [h, div_eq_mul_inv, fixedGaussianDenominator_mod_inv, mul_comm]

theorem fixedGaussianUnscaled_plus :
    fixedGaussianUnscaled 1 = (44 : ZMod 101) • fixedLiteralModPlus := by
  ext r k
  have h := congrArg (fun M : Matrix (Fin 48) (Fin 48) (ZMod 101) => M r k)
    fixedCanonicalMatrix_plus_mod
  change (fixedIntegerMatrix fixedIntegerBaseCanonical 1 r k : ZMod 101) =
    fixedLiteralModPlus r k at h
  change (fixedIntegerMatrix fixedIntegerBaseCanonical 1 r k : ZMod 101) /
    (fixedGaussianDenominator : ZMod 101) = 44 * fixedLiteralModPlus r k
  rw [h, div_eq_mul_inv, fixedGaussianDenominator_mod_inv, mul_comm]

theorem fixedGaussianUnscaled_minus :
    fixedGaussianUnscaled (-1) = (44 : ZMod 101) • fixedLiteralModMinus := by
  ext r k
  have h := congrArg (fun M : Matrix (Fin 48) (Fin 48) (ZMod 101) => M r k)
    fixedCanonicalMatrix_minus_mod
  change (fixedIntegerMatrix fixedIntegerBaseCanonical (-1) r k : ZMod 101) =
    fixedLiteralModMinus r k at h
  change (fixedIntegerMatrix fixedIntegerBaseCanonical (-1) r k : ZMod 101) /
    (fixedGaussianDenominator : ZMod 101) = 44 * fixedLiteralModMinus r k
  rw [h, div_eq_mul_inv, fixedGaussianDenominator_mod_inv, mul_comm]

end InternalCatalan

end

end

end OAI
