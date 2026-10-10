import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_7 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 59 (4 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (6 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-3 : ℤ)

def fixedRowPCoeff_7 (n : ℕ) : ℤ :=
    (if 59 = n then (4 : ℤ) else 0) +
    (if 60 = n then (-8 : ℤ) else 0) +
    (if 61 = n then (1 : ℤ) else 0) +
    (if 62 = n then (6 : ℤ) else 0) +
    (if 63 = n then (-3 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_7 (n : ℕ) :
    fixedRowPData_7.coeff n = fixedRowPCoeff_7 n := by
  simp only [fixedRowPData_7, fixedRowPCoeff_7, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_7 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_7 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_7, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_7 : ∀ k : Fin 63,
    fixedReversedTCoeff_3 (k.val + 2) - 2 * fixedReversedTCoeff_3 (k.val + 1) + fixedReversedTCoeff_3 k.val = fixedRowPCoeff_7 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_7 :
    (1 - X) ^ 2 * fixedReversedTData_3 = fixedRowPData_7 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_3, fixed_rowP_typed_coeff_7]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_3, fixed_rowP_typed_coeff_7]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_3, fixed_rowP_typed_coeff_7]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_7 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_3 _ (by omega),
              fixed_reversedT_typed_tail_3 _ (by omega), fixed_reversedT_typed_tail_3 _ hn',
              fixed_rowP_typed_tail_7 _ (by omega)]
            decide

theorem fixed_rowP_typed_7 : rowP 1 7 = fixedRowPData_7 := by
  calc
    rowP 1 7 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_3 :=
      fixedTyped_rowP_of_parameters 1 7 2 63 3 fixedChebyshevTData_3
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_3
    _ = fixedRowPData_7 := by
      rw [fixed_reversedT_typed_data_3, fixed_rowP_typed_factor_7]

def fixedRowDData_7 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 60 (4 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (3 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_7 (n : ℕ) : ℤ :=
    (if 60 = n then (4 : ℤ) else 0) +
    (if 61 = n then (-8 : ℤ) else 0) +
    (if 62 = n then (3 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_7 (n : ℕ) :
    fixedRowDData_7.coeff n = fixedRowDCoeff_7 n := by
  simp only [fixedRowDData_7, fixedRowDCoeff_7, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_7 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_7 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_7, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_7 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_2 (k.val + 2) - 2 * fixedReversedUCoeff_2 (k.val + 1) + fixedReversedUCoeff_2 k.val) = fixedRowDCoeff_7 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_7 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_2 = fixedRowDData_7 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_2, fixed_rowD_typed_coeff_7]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_2, fixed_rowD_typed_coeff_7]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_2, fixed_rowD_typed_coeff_7]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_7 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_2 _ (by omega),
              fixed_reversedU_typed_tail_2 _ (by omega), fixed_reversedU_typed_tail_2 _ hn',
              fixed_rowD_typed_tail_7 _ (by omega)]
            decide

theorem fixed_rowD_typed_7 : rowD 1 7 = fixedRowDData_7 := by
  calc
    rowD 1 7 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_2 :=
      fixedTyped_rowD_of_parameters 1 7 2 63 2 (1)
        fixedChebyshevUData_2 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_2
    _ = fixedRowDData_7 := by
      rw [fixed_reversedU_typed_data_2, fixed_rowD_typed_factor_7]

end InternalCatalan

end

end

end OAI
