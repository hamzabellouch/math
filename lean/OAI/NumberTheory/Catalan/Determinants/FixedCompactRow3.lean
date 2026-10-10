import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_3 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (1 : ℤ)

def fixedRowPCoeff_3 (n : ℕ) : ℤ :=
    (if 61 = n then (1 : ℤ) else 0) +
    (if 62 = n then (-2 : ℤ) else 0) +
    (if 63 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_3 (n : ℕ) :
    fixedRowPData_3.coeff n = fixedRowPCoeff_3 n := by
  simp only [fixedRowPData_3, fixedRowPCoeff_3, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_3 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_3 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_3, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_3 : ∀ k : Fin 63,
    fixedReversedTCoeff_1 (k.val + 2) - 2 * fixedReversedTCoeff_1 (k.val + 1) + fixedReversedTCoeff_1 k.val = fixedRowPCoeff_3 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_3 :
    (1 - X) ^ 2 * fixedReversedTData_1 = fixedRowPData_3 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_1, fixed_rowP_typed_coeff_3]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_1, fixed_rowP_typed_coeff_3]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_1, fixed_rowP_typed_coeff_3]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_3 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_1 _ (by omega),
              fixed_reversedT_typed_tail_1 _ (by omega), fixed_reversedT_typed_tail_1 _ hn',
              fixed_rowP_typed_tail_3 _ (by omega)]
            decide

theorem fixed_rowP_typed_3 : rowP 1 3 = fixedRowPData_3 := by
  calc
    rowP 1 3 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_1 :=
      fixedTyped_rowP_of_parameters 1 3 2 63 1 fixedChebyshevTData_1
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_1
    _ = fixedRowPData_3 := by
      rw [fixed_reversedT_typed_data_1, fixed_rowP_typed_factor_3]

def fixedRowDData_3 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_3 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_3 (n : ℕ) :
    fixedRowDData_3.coeff n = fixedRowDCoeff_3 n := by
  simp only [fixedRowDData_3, fixedRowDCoeff_3, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_3 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_3 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_3, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_3 : ∀ k : Fin 63,
    (-1 : ℤ) * (fixedReversedUCoeff_0 (k.val + 2) - 2 * fixedReversedUCoeff_0 (k.val + 1) + fixedReversedUCoeff_0 k.val) = fixedRowDCoeff_3 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_3 :
    Polynomial.C (-1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_0 = fixedRowDData_3 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_0, fixed_rowD_typed_coeff_3]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_0, fixed_rowD_typed_coeff_3]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_0, fixed_rowD_typed_coeff_3]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_3 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_0 _ (by omega),
              fixed_reversedU_typed_tail_0 _ (by omega), fixed_reversedU_typed_tail_0 _ hn',
              fixed_rowD_typed_tail_3 _ (by omega)]
            decide

theorem fixed_rowD_typed_3 : rowD 1 3 = fixedRowDData_3 := by
  calc
    rowD 1 3 = Polynomial.C (-1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_0 :=
      fixedTyped_rowD_of_parameters 1 3 2 63 0 (-1)
        fixedChebyshevUData_0 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_0
    _ = fixedRowDData_3 := by
      rw [fixed_reversedU_typed_data_0, fixed_rowD_typed_factor_3]

end InternalCatalan

end

end

end OAI
