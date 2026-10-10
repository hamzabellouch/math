import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT8To15
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU8To15

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_16 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 50 (2048 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-4096 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-4096 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (12288 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (768 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-13824 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (3328 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (7168 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-2744 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-1680 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (768 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (144 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-71 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_16 (n : ℕ) : ℤ :=
    (if 50 = n then (2048 : ℤ) else 0) +
    (if 51 = n then (-4096 : ℤ) else 0) +
    (if 52 = n then (-4096 : ℤ) else 0) +
    (if 53 = n then (12288 : ℤ) else 0) +
    (if 54 = n then (768 : ℤ) else 0) +
    (if 55 = n then (-13824 : ℤ) else 0) +
    (if 56 = n then (3328 : ℤ) else 0) +
    (if 57 = n then (7168 : ℤ) else 0) +
    (if 58 = n then (-2744 : ℤ) else 0) +
    (if 59 = n then (-1680 : ℤ) else 0) +
    (if 60 = n then (768 : ℤ) else 0) +
    (if 61 = n then (144 : ℤ) else 0) +
    (if 62 = n then (-71 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_16 (n : ℕ) :
    fixedRowPData_16.coeff n = fixedRowPCoeff_16 n := by
  simp only [fixedRowPData_16, fixedRowPCoeff_16, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_16 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_16 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_16, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_16 : ∀ k : Fin 63,
    fixedReversedTCoeff_12 (k.val + 2) - 2 * fixedReversedTCoeff_12 (k.val + 1) + fixedReversedTCoeff_12 k.val = fixedRowPCoeff_16 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_16 :
    (1 - X) ^ 2 * fixedReversedTData_12 = fixedRowPData_16 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_12, fixed_rowP_typed_coeff_16]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_12, fixed_rowP_typed_coeff_16]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_12, fixed_rowP_typed_coeff_16]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_16 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_12 _ (by omega),
              fixed_reversedT_typed_tail_12 _ (by omega), fixed_reversedT_typed_tail_12 _ hn',
              fixed_rowP_typed_tail_16 _ (by omega)]
            decide

theorem fixed_rowP_typed_16 : rowP 1 16 = fixedRowPData_16 := by
  calc
    rowP 1 16 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_12 :=
      fixedTyped_rowP_of_parameters 1 16 2 63 12 fixedChebyshevTData_12
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_12
    _ = fixedRowPData_16 := by
      rw [fixed_reversedT_typed_data_12, fixed_rowP_typed_factor_16]

def fixedRowDData_16 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 51 (2048 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-4096 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-3072 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (10240 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-512 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-9216 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (2816 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (3584 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-1512 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-560 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (268 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (24 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-12 : ℤ)

def fixedRowDCoeff_16 (n : ℕ) : ℤ :=
    (if 51 = n then (2048 : ℤ) else 0) +
    (if 52 = n then (-4096 : ℤ) else 0) +
    (if 53 = n then (-3072 : ℤ) else 0) +
    (if 54 = n then (10240 : ℤ) else 0) +
    (if 55 = n then (-512 : ℤ) else 0) +
    (if 56 = n then (-9216 : ℤ) else 0) +
    (if 57 = n then (2816 : ℤ) else 0) +
    (if 58 = n then (3584 : ℤ) else 0) +
    (if 59 = n then (-1512 : ℤ) else 0) +
    (if 60 = n then (-560 : ℤ) else 0) +
    (if 61 = n then (268 : ℤ) else 0) +
    (if 62 = n then (24 : ℤ) else 0) +
    (if 63 = n then (-12 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_16 (n : ℕ) :
    fixedRowDData_16.coeff n = fixedRowDCoeff_16 n := by
  simp only [fixedRowDData_16, fixedRowDCoeff_16, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_16 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_16 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_16, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_16 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_11 (k.val + 2) - 2 * fixedReversedUCoeff_11 (k.val + 1) + fixedReversedUCoeff_11 k.val) = fixedRowDCoeff_16 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_16 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_11 = fixedRowDData_16 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_11, fixed_rowD_typed_coeff_16]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_11, fixed_rowD_typed_coeff_16]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_11, fixed_rowD_typed_coeff_16]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_16 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_11 _ (by omega),
              fixed_reversedU_typed_tail_11 _ (by omega), fixed_reversedU_typed_tail_11 _ hn',
              fixed_rowD_typed_tail_16 _ (by omega)]
            decide

theorem fixed_rowD_typed_16 : rowD 1 16 = fixedRowDData_16 := by
  calc
    rowD 1 16 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_11 :=
      fixedTyped_rowD_of_parameters 1 16 2 63 11 (1)
        fixedChebyshevUData_11 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_11
    _ = fixedRowDData_16 := by
      rw [fixed_reversedU_typed_data_11, fixed_rowD_typed_factor_16]

end InternalCatalan

end

end

end OAI
