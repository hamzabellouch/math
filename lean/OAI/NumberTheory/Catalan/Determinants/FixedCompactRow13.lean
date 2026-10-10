import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT8To15
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU8To15

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_13 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 53 (256 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-512 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-320 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (1152 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-144 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-864 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (312 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (240 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-111 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-18 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (9 : ℤ)

def fixedRowPCoeff_13 (n : ℕ) : ℤ :=
    (if 53 = n then (256 : ℤ) else 0) +
    (if 54 = n then (-512 : ℤ) else 0) +
    (if 55 = n then (-320 : ℤ) else 0) +
    (if 56 = n then (1152 : ℤ) else 0) +
    (if 57 = n then (-144 : ℤ) else 0) +
    (if 58 = n then (-864 : ℤ) else 0) +
    (if 59 = n then (312 : ℤ) else 0) +
    (if 60 = n then (240 : ℤ) else 0) +
    (if 61 = n then (-111 : ℤ) else 0) +
    (if 62 = n then (-18 : ℤ) else 0) +
    (if 63 = n then (9 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_13 (n : ℕ) :
    fixedRowPData_13.coeff n = fixedRowPCoeff_13 n := by
  simp only [fixedRowPData_13, fixedRowPCoeff_13, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_13 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_13 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_13, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_13 : ∀ k : Fin 63,
    fixedReversedTCoeff_9 (k.val + 2) - 2 * fixedReversedTCoeff_9 (k.val + 1) + fixedReversedTCoeff_9 k.val = fixedRowPCoeff_13 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_13 :
    (1 - X) ^ 2 * fixedReversedTData_9 = fixedRowPData_13 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_9, fixed_rowP_typed_coeff_13]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_9, fixed_rowP_typed_coeff_13]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_9, fixed_rowP_typed_coeff_13]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_13 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_9 _ (by omega),
              fixed_reversedT_typed_tail_9 _ (by omega), fixed_reversedT_typed_tail_9 _ hn',
              fixed_rowP_typed_tail_13 _ (by omega)]
            decide

theorem fixed_rowP_typed_13 : rowP 1 13 = fixedRowPData_13 := by
  calc
    rowP 1 13 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_9 :=
      fixedTyped_rowP_of_parameters 1 13 2 63 9 fixedChebyshevTData_9
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_9
    _ = fixedRowPData_13 := by
      rw [fixed_reversedT_typed_data_9, fixed_rowP_typed_factor_13]

def fixedRowDData_13 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 54 (256 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-512 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-192 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (896 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-208 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-480 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (200 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (80 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-39 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_13 (n : ℕ) : ℤ :=
    (if 54 = n then (256 : ℤ) else 0) +
    (if 55 = n then (-512 : ℤ) else 0) +
    (if 56 = n then (-192 : ℤ) else 0) +
    (if 57 = n then (896 : ℤ) else 0) +
    (if 58 = n then (-208 : ℤ) else 0) +
    (if 59 = n then (-480 : ℤ) else 0) +
    (if 60 = n then (200 : ℤ) else 0) +
    (if 61 = n then (80 : ℤ) else 0) +
    (if 62 = n then (-39 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_13 (n : ℕ) :
    fixedRowDData_13.coeff n = fixedRowDCoeff_13 n := by
  simp only [fixedRowDData_13, fixedRowDCoeff_13, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_13 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_13 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_13, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_13 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_8 (k.val + 2) - 2 * fixedReversedUCoeff_8 (k.val + 1) + fixedReversedUCoeff_8 k.val) = fixedRowDCoeff_13 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_13 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_8 = fixedRowDData_13 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_8, fixed_rowD_typed_coeff_13]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_8, fixed_rowD_typed_coeff_13]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_8, fixed_rowD_typed_coeff_13]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_13 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_8 _ (by omega),
              fixed_reversedU_typed_tail_8 _ (by omega), fixed_reversedU_typed_tail_8 _ hn',
              fixed_rowD_typed_tail_13 _ (by omega)]
            decide

theorem fixed_rowD_typed_13 : rowD 1 13 = fixedRowDData_13 := by
  calc
    rowD 1 13 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_8 :=
      fixedTyped_rowD_of_parameters 1 13 2 63 8 (1)
        fixedChebyshevUData_8 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_8
    _ = fixedRowDData_13 := by
      rw [fixed_reversedU_typed_data_8, fixed_rowD_typed_factor_13]

end InternalCatalan

end

end

end OAI
