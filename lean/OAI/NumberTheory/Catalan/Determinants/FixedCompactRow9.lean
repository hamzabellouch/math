import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_9 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 57 (16 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-32 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-4 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (40 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-15 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-10 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (5 : ℤ)

def fixedRowPCoeff_9 (n : ℕ) : ℤ :=
    (if 57 = n then (16 : ℤ) else 0) +
    (if 58 = n then (-32 : ℤ) else 0) +
    (if 59 = n then (-4 : ℤ) else 0) +
    (if 60 = n then (40 : ℤ) else 0) +
    (if 61 = n then (-15 : ℤ) else 0) +
    (if 62 = n then (-10 : ℤ) else 0) +
    (if 63 = n then (5 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_9 (n : ℕ) :
    fixedRowPData_9.coeff n = fixedRowPCoeff_9 n := by
  simp only [fixedRowPData_9, fixedRowPCoeff_9, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_9 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_9 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_9, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_9 : ∀ k : Fin 63,
    fixedReversedTCoeff_5 (k.val + 2) - 2 * fixedReversedTCoeff_5 (k.val + 1) + fixedReversedTCoeff_5 k.val = fixedRowPCoeff_9 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_9 :
    (1 - X) ^ 2 * fixedReversedTData_5 = fixedRowPData_9 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_5, fixed_rowP_typed_coeff_9]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_5, fixed_rowP_typed_coeff_9]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_5, fixed_rowP_typed_coeff_9]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_9 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_5 _ (by omega),
              fixed_reversedT_typed_tail_5 _ (by omega), fixed_reversedT_typed_tail_5 _ hn',
              fixed_rowP_typed_tail_9 _ (by omega)]
            decide

theorem fixed_rowP_typed_9 : rowP 1 9 = fixedRowPData_9 := by
  calc
    rowP 1 9 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_5 :=
      fixedTyped_rowP_of_parameters 1 9 2 63 5 fixedChebyshevTData_5
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_5
    _ = fixedRowPData_9 := by
      rw [fixed_reversedT_typed_data_5, fixed_rowP_typed_factor_9]

def fixedRowDData_9 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 58 (16 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-32 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (4 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (24 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-11 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_9 (n : ℕ) : ℤ :=
    (if 58 = n then (16 : ℤ) else 0) +
    (if 59 = n then (-32 : ℤ) else 0) +
    (if 60 = n then (4 : ℤ) else 0) +
    (if 61 = n then (24 : ℤ) else 0) +
    (if 62 = n then (-11 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_9 (n : ℕ) :
    fixedRowDData_9.coeff n = fixedRowDCoeff_9 n := by
  simp only [fixedRowDData_9, fixedRowDCoeff_9, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_9 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_9 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_9, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_9 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_4 (k.val + 2) - 2 * fixedReversedUCoeff_4 (k.val + 1) + fixedReversedUCoeff_4 k.val) = fixedRowDCoeff_9 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_9 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_4 = fixedRowDData_9 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_4, fixed_rowD_typed_coeff_9]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_4, fixed_rowD_typed_coeff_9]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_4, fixed_rowD_typed_coeff_9]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_9 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_4 _ (by omega),
              fixed_reversedU_typed_tail_4 _ (by omega), fixed_reversedU_typed_tail_4 _ hn',
              fixed_rowD_typed_tail_9 _ (by omega)]
            decide

theorem fixed_rowD_typed_9 : rowD 1 9 = fixedRowDData_9 := by
  calc
    rowD 1 9 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_4 :=
      fixedTyped_rowD_of_parameters 1 9 2 63 4 (1)
        fixedChebyshevUData_4 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_4
    _ = fixedRowDData_9 := by
      rw [fixed_reversedU_typed_data_4, fixed_rowD_typed_factor_9]

end InternalCatalan

end

end

end OAI
