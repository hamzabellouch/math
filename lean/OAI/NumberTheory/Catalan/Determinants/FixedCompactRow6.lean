import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_6 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 60 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-4 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_6 (n : ℕ) : ℤ :=
    (if 60 = n then (2 : ℤ) else 0) +
    (if 61 = n then (-4 : ℤ) else 0) +
    (if 62 = n then (1 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_6 (n : ℕ) :
    fixedRowPData_6.coeff n = fixedRowPCoeff_6 n := by
  simp only [fixedRowPData_6, fixedRowPCoeff_6, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_6 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_6 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_6, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_6 : ∀ k : Fin 63,
    fixedReversedTCoeff_2 (k.val + 2) - 2 * fixedReversedTCoeff_2 (k.val + 1) + fixedReversedTCoeff_2 k.val = fixedRowPCoeff_6 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_6 :
    (1 - X) ^ 2 * fixedReversedTData_2 = fixedRowPData_6 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_2, fixed_rowP_typed_coeff_6]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_2, fixed_rowP_typed_coeff_6]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_2, fixed_rowP_typed_coeff_6]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_6 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_2 _ (by omega),
              fixed_reversedT_typed_tail_2 _ (by omega), fixed_reversedT_typed_tail_2 _ hn',
              fixed_rowP_typed_tail_6 _ (by omega)]
            decide

theorem fixed_rowP_typed_6 : rowP 1 6 = fixedRowPData_6 := by
  calc
    rowP 1 6 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_2 :=
      fixedTyped_rowP_of_parameters 1 6 2 63 2 fixedChebyshevTData_2
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_2
    _ = fixedRowPData_6 := by
      rw [fixed_reversedT_typed_data_2, fixed_rowP_typed_factor_6]

def fixedRowDData_6 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-4 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ)

def fixedRowDCoeff_6 (n : ℕ) : ℤ :=
    (if 61 = n then (2 : ℤ) else 0) +
    (if 62 = n then (-4 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_6 (n : ℕ) :
    fixedRowDData_6.coeff n = fixedRowDCoeff_6 n := by
  simp only [fixedRowDData_6, fixedRowDCoeff_6, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_6 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_6 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_6, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_6 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_1 (k.val + 2) - 2 * fixedReversedUCoeff_1 (k.val + 1) + fixedReversedUCoeff_1 k.val) = fixedRowDCoeff_6 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_6 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_1 = fixedRowDData_6 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_1, fixed_rowD_typed_coeff_6]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_1, fixed_rowD_typed_coeff_6]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_1, fixed_rowD_typed_coeff_6]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_6 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_1 _ (by omega),
              fixed_reversedU_typed_tail_1 _ (by omega), fixed_reversedU_typed_tail_1 _ hn',
              fixed_rowD_typed_tail_6 _ (by omega)]
            decide

theorem fixed_rowD_typed_6 : rowD 1 6 = fixedRowDData_6 := by
  calc
    rowD 1 6 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_1 :=
      fixedTyped_rowD_of_parameters 1 6 2 63 1 (1)
        fixedChebyshevUData_1 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_1
    _ = fixedRowDData_6 := by
      rw [fixed_reversedU_typed_data_1, fixed_rowD_typed_factor_6]

end InternalCatalan

end

end

end OAI
