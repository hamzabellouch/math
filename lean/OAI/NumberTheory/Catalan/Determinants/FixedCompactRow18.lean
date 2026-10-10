import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT8To15
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU8To15

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_18 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 48 (8192 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-16384 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-20480 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (57344 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (10752 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-78848 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (12544 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (53760 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-17472 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-18816 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (7840 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (3136 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-1470 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-196 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (97 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_18 (n : ℕ) : ℤ :=
    (if 48 = n then (8192 : ℤ) else 0) +
    (if 49 = n then (-16384 : ℤ) else 0) +
    (if 50 = n then (-20480 : ℤ) else 0) +
    (if 51 = n then (57344 : ℤ) else 0) +
    (if 52 = n then (10752 : ℤ) else 0) +
    (if 53 = n then (-78848 : ℤ) else 0) +
    (if 54 = n then (12544 : ℤ) else 0) +
    (if 55 = n then (53760 : ℤ) else 0) +
    (if 56 = n then (-17472 : ℤ) else 0) +
    (if 57 = n then (-18816 : ℤ) else 0) +
    (if 58 = n then (7840 : ℤ) else 0) +
    (if 59 = n then (3136 : ℤ) else 0) +
    (if 60 = n then (-1470 : ℤ) else 0) +
    (if 61 = n then (-196 : ℤ) else 0) +
    (if 62 = n then (97 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_18 (n : ℕ) :
    fixedRowPData_18.coeff n = fixedRowPCoeff_18 n := by
  simp only [fixedRowPData_18, fixedRowPCoeff_18, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_18 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_18 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_18, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_18 : ∀ k : Fin 63,
    fixedReversedTCoeff_14 (k.val + 2) - 2 * fixedReversedTCoeff_14 (k.val + 1) + fixedReversedTCoeff_14 k.val = fixedRowPCoeff_18 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_18 :
    (1 - X) ^ 2 * fixedReversedTData_14 = fixedRowPData_18 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_14, fixed_rowP_typed_coeff_18]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_14, fixed_rowP_typed_coeff_18]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_14, fixed_rowP_typed_coeff_18]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_18 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_14 _ (by omega),
              fixed_reversedT_typed_tail_14 _ (by omega), fixed_reversedT_typed_tail_14 _ hn',
              fixed_rowP_typed_tail_18 _ (by omega)]
            decide

theorem fixed_rowP_typed_18 : rowP 1 18 = fixedRowPData_18 := by
  calc
    rowP 1 18 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_14 :=
      fixedTyped_rowP_of_parameters 1 18 2 63 14 fixedChebyshevTData_14
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_14
    _ = fixedRowPData_18 := by
      rw [fixed_reversedT_typed_data_14, fixed_rowP_typed_factor_18]

def fixedRowDData_18 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 49 (8192 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-16384 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-16384 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (49152 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (3584 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-56320 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (12800 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (30720 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-11328 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-8064 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (3584 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (896 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-434 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-28 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (14 : ℤ)

def fixedRowDCoeff_18 (n : ℕ) : ℤ :=
    (if 49 = n then (8192 : ℤ) else 0) +
    (if 50 = n then (-16384 : ℤ) else 0) +
    (if 51 = n then (-16384 : ℤ) else 0) +
    (if 52 = n then (49152 : ℤ) else 0) +
    (if 53 = n then (3584 : ℤ) else 0) +
    (if 54 = n then (-56320 : ℤ) else 0) +
    (if 55 = n then (12800 : ℤ) else 0) +
    (if 56 = n then (30720 : ℤ) else 0) +
    (if 57 = n then (-11328 : ℤ) else 0) +
    (if 58 = n then (-8064 : ℤ) else 0) +
    (if 59 = n then (3584 : ℤ) else 0) +
    (if 60 = n then (896 : ℤ) else 0) +
    (if 61 = n then (-434 : ℤ) else 0) +
    (if 62 = n then (-28 : ℤ) else 0) +
    (if 63 = n then (14 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_18 (n : ℕ) :
    fixedRowDData_18.coeff n = fixedRowDCoeff_18 n := by
  simp only [fixedRowDData_18, fixedRowDCoeff_18, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_18 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_18 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_18, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_18 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_13 (k.val + 2) - 2 * fixedReversedUCoeff_13 (k.val + 1) + fixedReversedUCoeff_13 k.val) = fixedRowDCoeff_18 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_18 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_13 = fixedRowDData_18 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_13, fixed_rowD_typed_coeff_18]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_13, fixed_rowD_typed_coeff_18]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_13, fixed_rowD_typed_coeff_18]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_18 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_13 _ (by omega),
              fixed_reversedU_typed_tail_13 _ (by omega), fixed_reversedU_typed_tail_13 _ hn',
              fixed_rowD_typed_tail_18 _ (by omega)]
            decide

theorem fixed_rowD_typed_18 : rowD 1 18 = fixedRowDData_18 := by
  calc
    rowD 1 18 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_13 :=
      fixedTyped_rowD_of_parameters 1 18 2 63 13 (1)
        fixedChebyshevUData_13 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_13
    _ = fixedRowDData_18 := by
      rw [fixed_reversedU_typed_data_13, fixed_rowD_typed_factor_18]

end InternalCatalan

end

end

end OAI
