import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT8To15
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU8To15

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_14 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 52 (512 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1024 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-768 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (2560 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-160 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-2240 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (720 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (800 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-350 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-100 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (49 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_14 (n : ℕ) : ℤ :=
    (if 52 = n then (512 : ℤ) else 0) +
    (if 53 = n then (-1024 : ℤ) else 0) +
    (if 54 = n then (-768 : ℤ) else 0) +
    (if 55 = n then (2560 : ℤ) else 0) +
    (if 56 = n then (-160 : ℤ) else 0) +
    (if 57 = n then (-2240 : ℤ) else 0) +
    (if 58 = n then (720 : ℤ) else 0) +
    (if 59 = n then (800 : ℤ) else 0) +
    (if 60 = n then (-350 : ℤ) else 0) +
    (if 61 = n then (-100 : ℤ) else 0) +
    (if 62 = n then (49 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_14 (n : ℕ) :
    fixedRowPData_14.coeff n = fixedRowPCoeff_14 n := by
  simp only [fixedRowPData_14, fixedRowPCoeff_14, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_14 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_14 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_14, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_14 : ∀ k : Fin 63,
    fixedReversedTCoeff_10 (k.val + 2) - 2 * fixedReversedTCoeff_10 (k.val + 1) + fixedReversedTCoeff_10 k.val = fixedRowPCoeff_14 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_14 :
    (1 - X) ^ 2 * fixedReversedTData_10 = fixedRowPData_14 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_10, fixed_rowP_typed_coeff_14]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_10, fixed_rowP_typed_coeff_14]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_10, fixed_rowP_typed_coeff_14]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_14 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_10 _ (by omega),
              fixed_reversedT_typed_tail_10 _ (by omega), fixed_reversedT_typed_tail_10 _ hn',
              fixed_rowP_typed_tail_14 _ (by omega)]
            decide

theorem fixed_rowP_typed_14 : rowP 1 14 = fixedRowPData_14 := by
  calc
    rowP 1 14 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_10 :=
      fixedTyped_rowP_of_parameters 1 14 2 63 10 fixedChebyshevTData_10
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_10
    _ = fixedRowPData_14 := by
      rw [fixed_reversedT_typed_data_10, fixed_rowP_typed_factor_14]

def fixedRowDData_14 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 53 (512 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-1024 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-512 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (2048 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-352 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-1344 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (512 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (320 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-150 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-20 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (10 : ℤ)

def fixedRowDCoeff_14 (n : ℕ) : ℤ :=
    (if 53 = n then (512 : ℤ) else 0) +
    (if 54 = n then (-1024 : ℤ) else 0) +
    (if 55 = n then (-512 : ℤ) else 0) +
    (if 56 = n then (2048 : ℤ) else 0) +
    (if 57 = n then (-352 : ℤ) else 0) +
    (if 58 = n then (-1344 : ℤ) else 0) +
    (if 59 = n then (512 : ℤ) else 0) +
    (if 60 = n then (320 : ℤ) else 0) +
    (if 61 = n then (-150 : ℤ) else 0) +
    (if 62 = n then (-20 : ℤ) else 0) +
    (if 63 = n then (10 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_14 (n : ℕ) :
    fixedRowDData_14.coeff n = fixedRowDCoeff_14 n := by
  simp only [fixedRowDData_14, fixedRowDCoeff_14, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_14 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_14 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_14, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_14 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_9 (k.val + 2) - 2 * fixedReversedUCoeff_9 (k.val + 1) + fixedReversedUCoeff_9 k.val) = fixedRowDCoeff_14 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_14 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_9 = fixedRowDData_14 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_9, fixed_rowD_typed_coeff_14]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_9, fixed_rowD_typed_coeff_14]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_9, fixed_rowD_typed_coeff_14]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_14 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_9 _ (by omega),
              fixed_reversedU_typed_tail_9 _ (by omega), fixed_reversedU_typed_tail_9 _ hn',
              fixed_rowD_typed_tail_14 _ (by omega)]
            decide

theorem fixed_rowD_typed_14 : rowD 1 14 = fixedRowDData_14 := by
  calc
    rowD 1 14 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_9 :=
      fixedTyped_rowD_of_parameters 1 14 2 63 9 (1)
        fixedChebyshevUData_9 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_9
    _ = fixedRowDData_14 := by
      rw [fixed_reversedU_typed_data_9, fixed_rowD_typed_factor_14]

end InternalCatalan

end

end

end OAI
