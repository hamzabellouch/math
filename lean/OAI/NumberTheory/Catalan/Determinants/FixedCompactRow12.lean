import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT8To15
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_12 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 54 (128 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-256 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-128 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (512 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-96 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-320 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (128 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (64 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-31 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_12 (n : ℕ) : ℤ :=
    (if 54 = n then (128 : ℤ) else 0) +
    (if 55 = n then (-256 : ℤ) else 0) +
    (if 56 = n then (-128 : ℤ) else 0) +
    (if 57 = n then (512 : ℤ) else 0) +
    (if 58 = n then (-96 : ℤ) else 0) +
    (if 59 = n then (-320 : ℤ) else 0) +
    (if 60 = n then (128 : ℤ) else 0) +
    (if 61 = n then (64 : ℤ) else 0) +
    (if 62 = n then (-31 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_12 (n : ℕ) :
    fixedRowPData_12.coeff n = fixedRowPCoeff_12 n := by
  simp only [fixedRowPData_12, fixedRowPCoeff_12, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_12 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_12 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_12, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_12 : ∀ k : Fin 63,
    fixedReversedTCoeff_8 (k.val + 2) - 2 * fixedReversedTCoeff_8 (k.val + 1) + fixedReversedTCoeff_8 k.val = fixedRowPCoeff_12 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_12 :
    (1 - X) ^ 2 * fixedReversedTData_8 = fixedRowPData_12 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_8, fixed_rowP_typed_coeff_12]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_8, fixed_rowP_typed_coeff_12]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_8, fixed_rowP_typed_coeff_12]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_12 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_8 _ (by omega),
              fixed_reversedT_typed_tail_8 _ (by omega), fixed_reversedT_typed_tail_8 _ hn',
              fixed_rowP_typed_tail_12 _ (by omega)]
            decide

theorem fixed_rowP_typed_12 : rowP 1 12 = fixedRowPData_12 := by
  calc
    rowP 1 12 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_8 :=
      fixedTyped_rowP_of_parameters 1 12 2 63 8 fixedChebyshevTData_8
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_8
    _ = fixedRowPData_12 := by
      rw [fixed_reversedT_typed_data_8, fixed_rowP_typed_factor_12]

def fixedRowDData_12 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 55 (128 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-256 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-64 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (384 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-112 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-160 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (72 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (16 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-8 : ℤ)

def fixedRowDCoeff_12 (n : ℕ) : ℤ :=
    (if 55 = n then (128 : ℤ) else 0) +
    (if 56 = n then (-256 : ℤ) else 0) +
    (if 57 = n then (-64 : ℤ) else 0) +
    (if 58 = n then (384 : ℤ) else 0) +
    (if 59 = n then (-112 : ℤ) else 0) +
    (if 60 = n then (-160 : ℤ) else 0) +
    (if 61 = n then (72 : ℤ) else 0) +
    (if 62 = n then (16 : ℤ) else 0) +
    (if 63 = n then (-8 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_12 (n : ℕ) :
    fixedRowDData_12.coeff n = fixedRowDCoeff_12 n := by
  simp only [fixedRowDData_12, fixedRowDCoeff_12, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_12 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_12 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_12, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_12 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_7 (k.val + 2) - 2 * fixedReversedUCoeff_7 (k.val + 1) + fixedReversedUCoeff_7 k.val) = fixedRowDCoeff_12 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_12 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_7 = fixedRowDData_12 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_7, fixed_rowD_typed_coeff_12]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_7, fixed_rowD_typed_coeff_12]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_7, fixed_rowD_typed_coeff_12]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_12 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_7 _ (by omega),
              fixed_reversedU_typed_tail_7 _ (by omega), fixed_reversedU_typed_tail_7 _ hn',
              fixed_rowD_typed_tail_12 _ (by omega)]
            decide

theorem fixed_rowD_typed_12 : rowD 1 12 = fixedRowDData_12 := by
  calc
    rowD 1 12 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_7 :=
      fixedTyped_rowD_of_parameters 1 12 2 63 7 (1)
        fixedChebyshevUData_7 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_7
    _ = fixedRowDData_12 := by
      rw [fixed_reversedU_typed_data_7, fixed_rowD_typed_factor_12]

end InternalCatalan

end

end

end OAI
