import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT8To15
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU8To15

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_15 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 51 (1024 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-2048 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1792 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (5632 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-5632 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (1584 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (2464 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-1012 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-440 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (209 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (22 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-11 : ℤ)

def fixedRowPCoeff_15 (n : ℕ) : ℤ :=
    (if 51 = n then (1024 : ℤ) else 0) +
    (if 52 = n then (-2048 : ℤ) else 0) +
    (if 53 = n then (-1792 : ℤ) else 0) +
    (if 54 = n then (5632 : ℤ) else 0) +
    (if 56 = n then (-5632 : ℤ) else 0) +
    (if 57 = n then (1584 : ℤ) else 0) +
    (if 58 = n then (2464 : ℤ) else 0) +
    (if 59 = n then (-1012 : ℤ) else 0) +
    (if 60 = n then (-440 : ℤ) else 0) +
    (if 61 = n then (209 : ℤ) else 0) +
    (if 62 = n then (22 : ℤ) else 0) +
    (if 63 = n then (-11 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_15 (n : ℕ) :
    fixedRowPData_15.coeff n = fixedRowPCoeff_15 n := by
  simp only [fixedRowPData_15, fixedRowPCoeff_15, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_15 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_15 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_15, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_15 : ∀ k : Fin 63,
    fixedReversedTCoeff_11 (k.val + 2) - 2 * fixedReversedTCoeff_11 (k.val + 1) + fixedReversedTCoeff_11 k.val = fixedRowPCoeff_15 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_15 :
    (1 - X) ^ 2 * fixedReversedTData_11 = fixedRowPData_15 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_11, fixed_rowP_typed_coeff_15]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_11, fixed_rowP_typed_coeff_15]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_11, fixed_rowP_typed_coeff_15]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_15 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_11 _ (by omega),
              fixed_reversedT_typed_tail_11 _ (by omega), fixed_reversedT_typed_tail_11 _ hn',
              fixed_rowP_typed_tail_15 _ (by omega)]
            decide

theorem fixed_rowP_typed_15 : rowP 1 15 = fixedRowPData_15 := by
  calc
    rowP 1 15 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_11 :=
      fixedTyped_rowP_of_parameters 1 15 2 63 11 fixedChebyshevTData_11
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_11
    _ = fixedRowPData_15 := by
      rw [fixed_reversedT_typed_data_11, fixed_rowP_typed_factor_15]

def fixedRowDData_15 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 52 (1024 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-2048 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-1280 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (4608 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-512 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-3584 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (1232 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (1120 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-500 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-120 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (59 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_15 (n : ℕ) : ℤ :=
    (if 52 = n then (1024 : ℤ) else 0) +
    (if 53 = n then (-2048 : ℤ) else 0) +
    (if 54 = n then (-1280 : ℤ) else 0) +
    (if 55 = n then (4608 : ℤ) else 0) +
    (if 56 = n then (-512 : ℤ) else 0) +
    (if 57 = n then (-3584 : ℤ) else 0) +
    (if 58 = n then (1232 : ℤ) else 0) +
    (if 59 = n then (1120 : ℤ) else 0) +
    (if 60 = n then (-500 : ℤ) else 0) +
    (if 61 = n then (-120 : ℤ) else 0) +
    (if 62 = n then (59 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_15 (n : ℕ) :
    fixedRowDData_15.coeff n = fixedRowDCoeff_15 n := by
  simp only [fixedRowDData_15, fixedRowDCoeff_15, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_15 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_15 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_15, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_15 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_10 (k.val + 2) - 2 * fixedReversedUCoeff_10 (k.val + 1) + fixedReversedUCoeff_10 k.val) = fixedRowDCoeff_15 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_15 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_10 = fixedRowDData_15 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_10, fixed_rowD_typed_coeff_15]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_10, fixed_rowD_typed_coeff_15]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_10, fixed_rowD_typed_coeff_15]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_15 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_10 _ (by omega),
              fixed_reversedU_typed_tail_10 _ (by omega), fixed_reversedU_typed_tail_10 _ hn',
              fixed_rowD_typed_tail_15 _ (by omega)]
            decide

theorem fixed_rowD_typed_15 : rowD 1 15 = fixedRowDData_15 := by
  calc
    rowD 1 15 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_10 :=
      fixedTyped_rowD_of_parameters 1 15 2 63 10 (1)
        fixedChebyshevUData_10 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_10
    _ = fixedRowDData_15 := by
      rw [fixed_reversedU_typed_data_10, fixed_rowD_typed_factor_15]

end InternalCatalan

end

end

end OAI
