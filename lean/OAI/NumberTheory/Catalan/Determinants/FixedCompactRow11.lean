import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_11 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 55 (64 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-128 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-48 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (224 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-56 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-112 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (49 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (14 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-7 : ℤ)

def fixedRowPCoeff_11 (n : ℕ) : ℤ :=
    (if 55 = n then (64 : ℤ) else 0) +
    (if 56 = n then (-128 : ℤ) else 0) +
    (if 57 = n then (-48 : ℤ) else 0) +
    (if 58 = n then (224 : ℤ) else 0) +
    (if 59 = n then (-56 : ℤ) else 0) +
    (if 60 = n then (-112 : ℤ) else 0) +
    (if 61 = n then (49 : ℤ) else 0) +
    (if 62 = n then (14 : ℤ) else 0) +
    (if 63 = n then (-7 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_11 (n : ℕ) :
    fixedRowPData_11.coeff n = fixedRowPCoeff_11 n := by
  simp only [fixedRowPData_11, fixedRowPCoeff_11, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_11 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_11 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_11, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_11 : ∀ k : Fin 63,
    fixedReversedTCoeff_7 (k.val + 2) - 2 * fixedReversedTCoeff_7 (k.val + 1) + fixedReversedTCoeff_7 k.val = fixedRowPCoeff_11 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_11 :
    (1 - X) ^ 2 * fixedReversedTData_7 = fixedRowPData_11 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_7, fixed_rowP_typed_coeff_11]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_7, fixed_rowP_typed_coeff_11]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_7, fixed_rowP_typed_coeff_11]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_11 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_7 _ (by omega),
              fixed_reversedT_typed_tail_7 _ (by omega), fixed_reversedT_typed_tail_7 _ hn',
              fixed_rowP_typed_tail_11 _ (by omega)]
            decide

theorem fixed_rowP_typed_11 : rowP 1 11 = fixedRowPData_11 := by
  calc
    rowP 1 11 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_7 :=
      fixedTyped_rowP_of_parameters 1 11 2 63 7 fixedChebyshevTData_7
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_7
    _ = fixedRowPData_11 := by
      rw [fixed_reversedT_typed_data_7, fixed_rowP_typed_factor_11]

def fixedRowDData_11 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 56 (64 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-128 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-16 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (160 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-56 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-48 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (23 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_11 (n : ℕ) : ℤ :=
    (if 56 = n then (64 : ℤ) else 0) +
    (if 57 = n then (-128 : ℤ) else 0) +
    (if 58 = n then (-16 : ℤ) else 0) +
    (if 59 = n then (160 : ℤ) else 0) +
    (if 60 = n then (-56 : ℤ) else 0) +
    (if 61 = n then (-48 : ℤ) else 0) +
    (if 62 = n then (23 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_11 (n : ℕ) :
    fixedRowDData_11.coeff n = fixedRowDCoeff_11 n := by
  simp only [fixedRowDData_11, fixedRowDCoeff_11, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_11 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_11 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_11, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_11 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_6 (k.val + 2) - 2 * fixedReversedUCoeff_6 (k.val + 1) + fixedReversedUCoeff_6 k.val) = fixedRowDCoeff_11 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_11 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_6 = fixedRowDData_11 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_6, fixed_rowD_typed_coeff_11]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_6, fixed_rowD_typed_coeff_11]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_6, fixed_rowD_typed_coeff_11]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_11 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_6 _ (by omega),
              fixed_reversedU_typed_tail_6 _ (by omega), fixed_reversedU_typed_tail_6 _ hn',
              fixed_rowD_typed_tail_11 _ (by omega)]
            decide

theorem fixed_rowD_typed_11 : rowD 1 11 = fixedRowDData_11 := by
  calc
    rowD 1 11 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_6 :=
      fixedTyped_rowD_of_parameters 1 11 2 63 6 (1)
        fixedChebyshevUData_6 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_6
    _ = fixedRowDData_11 := by
      rw [fixed_reversedU_typed_data_6, fixed_rowD_typed_factor_11]

end InternalCatalan

end

end

end OAI
