import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_1 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 59 (4 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (6 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-3 : ℤ)

def fixedRowPCoeff_1 (n : ℕ) : ℤ :=
    (if 59 = n then (4 : ℤ) else 0) +
    (if 60 = n then (-8 : ℤ) else 0) +
    (if 61 = n then (1 : ℤ) else 0) +
    (if 62 = n then (6 : ℤ) else 0) +
    (if 63 = n then (-3 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_1 (n : ℕ) :
    fixedRowPData_1.coeff n = fixedRowPCoeff_1 n := by
  simp only [fixedRowPData_1, fixedRowPCoeff_1, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_1 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_1 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_1, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_1 : ∀ k : Fin 63,
    fixedReversedTCoeff_3 (k.val + 2) - 2 * fixedReversedTCoeff_3 (k.val + 1) + fixedReversedTCoeff_3 k.val = fixedRowPCoeff_1 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_1 :
    (1 - X) ^ 2 * fixedReversedTData_3 = fixedRowPData_1 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_3, fixed_rowP_typed_coeff_1]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_3, fixed_rowP_typed_coeff_1]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_3, fixed_rowP_typed_coeff_1]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_1 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_3 _ (by omega),
              fixed_reversedT_typed_tail_3 _ (by omega), fixed_reversedT_typed_tail_3 _ hn',
              fixed_rowP_typed_tail_1 _ (by omega)]
            decide

theorem fixed_rowP_typed_1 : rowP 1 1 = fixedRowPData_1 := by
  calc
    rowP 1 1 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_3 :=
      fixedTyped_rowP_of_parameters 1 1 2 63 3 fixedChebyshevTData_3
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_3
    _ = fixedRowPData_1 := by
      rw [fixed_reversedT_typed_data_3, fixed_rowP_typed_factor_1]

def fixedRowDData_1 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 60 (-4 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (8 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-3 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_1 (n : ℕ) : ℤ :=
    (if 60 = n then (-4 : ℤ) else 0) +
    (if 61 = n then (8 : ℤ) else 0) +
    (if 62 = n then (-3 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_1 (n : ℕ) :
    fixedRowDData_1.coeff n = fixedRowDCoeff_1 n := by
  simp only [fixedRowDData_1, fixedRowDCoeff_1, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_1 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_1 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_1, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_1 : ∀ k : Fin 63,
    (-1 : ℤ) * (fixedReversedUCoeff_2 (k.val + 2) - 2 * fixedReversedUCoeff_2 (k.val + 1) + fixedReversedUCoeff_2 k.val) = fixedRowDCoeff_1 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_1 :
    Polynomial.C (-1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_2 = fixedRowDData_1 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_2, fixed_rowD_typed_coeff_1]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_2, fixed_rowD_typed_coeff_1]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_2, fixed_rowD_typed_coeff_1]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_1 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_2 _ (by omega),
              fixed_reversedU_typed_tail_2 _ (by omega), fixed_reversedU_typed_tail_2 _ hn',
              fixed_rowD_typed_tail_1 _ (by omega)]
            decide

theorem fixed_rowD_typed_1 : rowD 1 1 = fixedRowDData_1 := by
  calc
    rowD 1 1 = Polynomial.C (-1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_2 :=
      fixedTyped_rowD_of_parameters 1 1 2 63 2 (-1)
        fixedChebyshevUData_2 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_2
    _ = fixedRowDData_1 := by
      rw [fixed_reversedU_typed_data_2, fixed_rowD_typed_factor_1]

end InternalCatalan

end

end

end OAI
