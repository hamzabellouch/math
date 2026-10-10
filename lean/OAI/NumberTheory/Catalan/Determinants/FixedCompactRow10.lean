import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_10 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 56 (32 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-64 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-16 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (96 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-30 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-36 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (17 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_10 (n : ℕ) : ℤ :=
    (if 56 = n then (32 : ℤ) else 0) +
    (if 57 = n then (-64 : ℤ) else 0) +
    (if 58 = n then (-16 : ℤ) else 0) +
    (if 59 = n then (96 : ℤ) else 0) +
    (if 60 = n then (-30 : ℤ) else 0) +
    (if 61 = n then (-36 : ℤ) else 0) +
    (if 62 = n then (17 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_10 (n : ℕ) :
    fixedRowPData_10.coeff n = fixedRowPCoeff_10 n := by
  simp only [fixedRowPData_10, fixedRowPCoeff_10, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_10 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_10 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_10, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_10 : ∀ k : Fin 63,
    fixedReversedTCoeff_6 (k.val + 2) - 2 * fixedReversedTCoeff_6 (k.val + 1) + fixedReversedTCoeff_6 k.val = fixedRowPCoeff_10 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_10 :
    (1 - X) ^ 2 * fixedReversedTData_6 = fixedRowPData_10 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_6, fixed_rowP_typed_coeff_10]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_6, fixed_rowP_typed_coeff_10]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_6, fixed_rowP_typed_coeff_10]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_10 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_6 _ (by omega),
              fixed_reversedT_typed_tail_6 _ (by omega), fixed_reversedT_typed_tail_6 _ hn',
              fixed_rowP_typed_tail_10 _ (by omega)]
            decide

theorem fixed_rowP_typed_10 : rowP 1 10 = fixedRowPData_10 := by
  calc
    rowP 1 10 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_6 :=
      fixedTyped_rowP_of_parameters 1 10 2 63 6 fixedChebyshevTData_6
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_6
    _ = fixedRowPData_10 := by
      rw [fixed_reversedT_typed_data_6, fixed_rowP_typed_factor_10]

def fixedRowDData_10 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 57 (32 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-64 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (64 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-26 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-12 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (6 : ℤ)

def fixedRowDCoeff_10 (n : ℕ) : ℤ :=
    (if 57 = n then (32 : ℤ) else 0) +
    (if 58 = n then (-64 : ℤ) else 0) +
    (if 60 = n then (64 : ℤ) else 0) +
    (if 61 = n then (-26 : ℤ) else 0) +
    (if 62 = n then (-12 : ℤ) else 0) +
    (if 63 = n then (6 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_10 (n : ℕ) :
    fixedRowDData_10.coeff n = fixedRowDCoeff_10 n := by
  simp only [fixedRowDData_10, fixedRowDCoeff_10, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_10 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_10 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_10, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_10 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_5 (k.val + 2) - 2 * fixedReversedUCoeff_5 (k.val + 1) + fixedReversedUCoeff_5 k.val) = fixedRowDCoeff_10 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_10 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_5 = fixedRowDData_10 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_5, fixed_rowD_typed_coeff_10]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_5, fixed_rowD_typed_coeff_10]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_5, fixed_rowD_typed_coeff_10]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_10 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_5 _ (by omega),
              fixed_reversedU_typed_tail_5 _ (by omega), fixed_reversedU_typed_tail_5 _ hn',
              fixed_rowD_typed_tail_10 _ (by omega)]
            decide

theorem fixed_rowD_typed_10 : rowD 1 10 = fixedRowDData_10 := by
  calc
    rowD 1 10 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_5 :=
      fixedTyped_rowD_of_parameters 1 10 2 63 5 (1)
        fixedChebyshevUData_5 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_5
    _ = fixedRowDData_10 := by
      rw [fixed_reversedU_typed_data_5, fixed_rowD_typed_factor_10]

end InternalCatalan

end

end

end OAI
