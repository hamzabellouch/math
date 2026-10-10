import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT8To15
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU8To15

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_17 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 49 (4096 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-8192 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-9216 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (26624 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (3328 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-33280 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (6656 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (19968 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-7072 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-5824 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (2548 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (728 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-351 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-26 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (13 : ℤ)

def fixedRowPCoeff_17 (n : ℕ) : ℤ :=
    (if 49 = n then (4096 : ℤ) else 0) +
    (if 50 = n then (-8192 : ℤ) else 0) +
    (if 51 = n then (-9216 : ℤ) else 0) +
    (if 52 = n then (26624 : ℤ) else 0) +
    (if 53 = n then (3328 : ℤ) else 0) +
    (if 54 = n then (-33280 : ℤ) else 0) +
    (if 55 = n then (6656 : ℤ) else 0) +
    (if 56 = n then (19968 : ℤ) else 0) +
    (if 57 = n then (-7072 : ℤ) else 0) +
    (if 58 = n then (-5824 : ℤ) else 0) +
    (if 59 = n then (2548 : ℤ) else 0) +
    (if 60 = n then (728 : ℤ) else 0) +
    (if 61 = n then (-351 : ℤ) else 0) +
    (if 62 = n then (-26 : ℤ) else 0) +
    (if 63 = n then (13 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_17 (n : ℕ) :
    fixedRowPData_17.coeff n = fixedRowPCoeff_17 n := by
  simp only [fixedRowPData_17, fixedRowPCoeff_17, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_17 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_17 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_17, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_17 : ∀ k : Fin 63,
    fixedReversedTCoeff_13 (k.val + 2) - 2 * fixedReversedTCoeff_13 (k.val + 1) + fixedReversedTCoeff_13 k.val = fixedRowPCoeff_17 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_17 :
    (1 - X) ^ 2 * fixedReversedTData_13 = fixedRowPData_17 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_13, fixed_rowP_typed_coeff_17]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_13, fixed_rowP_typed_coeff_17]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_13, fixed_rowP_typed_coeff_17]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_17 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_13 _ (by omega),
              fixed_reversedT_typed_tail_13 _ (by omega), fixed_reversedT_typed_tail_13 _ hn',
              fixed_rowP_typed_tail_17 _ (by omega)]
            decide

theorem fixed_rowP_typed_17 : rowP 1 17 = fixedRowPData_17 := by
  calc
    rowP 1 17 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_13 :=
      fixedTyped_rowP_of_parameters 1 17 2 63 13 fixedChebyshevTData_13
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_13
    _ = fixedRowPData_17 := by
      rw [fixed_reversedT_typed_data_13, fixed_rowP_typed_factor_17]

def fixedRowDData_17 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 50 (4096 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-8192 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-7168 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (22528 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (256 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-23040 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (6144 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (10752 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-4256 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-2240 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (1036 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (168 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-83 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_17 (n : ℕ) : ℤ :=
    (if 50 = n then (4096 : ℤ) else 0) +
    (if 51 = n then (-8192 : ℤ) else 0) +
    (if 52 = n then (-7168 : ℤ) else 0) +
    (if 53 = n then (22528 : ℤ) else 0) +
    (if 54 = n then (256 : ℤ) else 0) +
    (if 55 = n then (-23040 : ℤ) else 0) +
    (if 56 = n then (6144 : ℤ) else 0) +
    (if 57 = n then (10752 : ℤ) else 0) +
    (if 58 = n then (-4256 : ℤ) else 0) +
    (if 59 = n then (-2240 : ℤ) else 0) +
    (if 60 = n then (1036 : ℤ) else 0) +
    (if 61 = n then (168 : ℤ) else 0) +
    (if 62 = n then (-83 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_17 (n : ℕ) :
    fixedRowDData_17.coeff n = fixedRowDCoeff_17 n := by
  simp only [fixedRowDData_17, fixedRowDCoeff_17, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_17 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_17 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_17, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_17 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_12 (k.val + 2) - 2 * fixedReversedUCoeff_12 (k.val + 1) + fixedReversedUCoeff_12 k.val) = fixedRowDCoeff_17 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_17 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_12 = fixedRowDData_17 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_12, fixed_rowD_typed_coeff_17]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_12, fixed_rowD_typed_coeff_17]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_12, fixed_rowD_typed_coeff_17]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_17 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_12 _ (by omega),
              fixed_reversedU_typed_tail_12 _ (by omega), fixed_reversedU_typed_tail_12 _ hn',
              fixed_rowD_typed_tail_17 _ (by omega)]
            decide

theorem fixed_rowD_typed_17 : rowD 1 17 = fixedRowDData_17 := by
  calc
    rowD 1 17 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_12 :=
      fixedTyped_rowD_of_parameters 1 17 2 63 12 (1)
        fixedChebyshevUData_12 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_12
    _ = fixedRowDData_17 := by
      rw [fixed_reversedU_typed_data_12, fixed_rowD_typed_factor_17]

end InternalCatalan

end

end

end OAI
