import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT16To23
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU16To23

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_25 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 41 (1048576 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-2097152 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-4456448 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (11010048 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (6881280 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-24772608 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-3211264 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (31195136 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-3555328 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-24084480 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (6171648 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (11741184 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-4076800 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-3587584 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (1464320 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (658944 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-296208 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-66528 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (31724 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (3080 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-1519 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-42 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (21 : ℤ)

def fixedRowPCoeff_25 (n : ℕ) : ℤ :=
    (if 41 = n then (1048576 : ℤ) else 0) +
    (if 42 = n then (-2097152 : ℤ) else 0) +
    (if 43 = n then (-4456448 : ℤ) else 0) +
    (if 44 = n then (11010048 : ℤ) else 0) +
    (if 45 = n then (6881280 : ℤ) else 0) +
    (if 46 = n then (-24772608 : ℤ) else 0) +
    (if 47 = n then (-3211264 : ℤ) else 0) +
    (if 48 = n then (31195136 : ℤ) else 0) +
    (if 49 = n then (-3555328 : ℤ) else 0) +
    (if 50 = n then (-24084480 : ℤ) else 0) +
    (if 51 = n then (6171648 : ℤ) else 0) +
    (if 52 = n then (11741184 : ℤ) else 0) +
    (if 53 = n then (-4076800 : ℤ) else 0) +
    (if 54 = n then (-3587584 : ℤ) else 0) +
    (if 55 = n then (1464320 : ℤ) else 0) +
    (if 56 = n then (658944 : ℤ) else 0) +
    (if 57 = n then (-296208 : ℤ) else 0) +
    (if 58 = n then (-66528 : ℤ) else 0) +
    (if 59 = n then (31724 : ℤ) else 0) +
    (if 60 = n then (3080 : ℤ) else 0) +
    (if 61 = n then (-1519 : ℤ) else 0) +
    (if 62 = n then (-42 : ℤ) else 0) +
    (if 63 = n then (21 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_25 (n : ℕ) :
    fixedRowPData_25.coeff n = fixedRowPCoeff_25 n := by
  simp only [fixedRowPData_25, fixedRowPCoeff_25, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_25 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_25 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_25, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_25 : ∀ k : Fin 63,
    fixedReversedTCoeff_21 (k.val + 2) - 2 * fixedReversedTCoeff_21 (k.val + 1) + fixedReversedTCoeff_21 k.val = fixedRowPCoeff_25 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_25 :
    (1 - X) ^ 2 * fixedReversedTData_21 = fixedRowPData_25 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_21, fixed_rowP_typed_coeff_25]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_21, fixed_rowP_typed_coeff_25]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_21, fixed_rowP_typed_coeff_25]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_25 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_21 _ (by omega),
              fixed_reversedT_typed_tail_21 _ (by omega), fixed_reversedT_typed_tail_21 _ hn',
              fixed_rowP_typed_tail_25 _ (by omega)]
            decide

theorem fixed_rowP_typed_25 : rowP 1 25 = fixedRowPData_25 := by
  calc
    rowP 1 25 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_21 :=
      fixedTyped_rowP_of_parameters 1 25 2 63 21 fixedChebyshevTData_21
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_21
    _ = fixedRowPData_25 := by
      rw [fixed_reversedT_typed_data_21, fixed_rowP_typed_factor_25]

def fixedRowDData_25 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 42 (1048576 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-2097152 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-3932160 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (9961472 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (5046272 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-20054016 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-1114112 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (22282240 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-3686400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-14909440 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (4379648 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (6150144 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-2306304 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-1537536 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (658944 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (219648 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-101904 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-15840 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (7700 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (440 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-219 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_25 (n : ℕ) : ℤ :=
    (if 42 = n then (1048576 : ℤ) else 0) +
    (if 43 = n then (-2097152 : ℤ) else 0) +
    (if 44 = n then (-3932160 : ℤ) else 0) +
    (if 45 = n then (9961472 : ℤ) else 0) +
    (if 46 = n then (5046272 : ℤ) else 0) +
    (if 47 = n then (-20054016 : ℤ) else 0) +
    (if 48 = n then (-1114112 : ℤ) else 0) +
    (if 49 = n then (22282240 : ℤ) else 0) +
    (if 50 = n then (-3686400 : ℤ) else 0) +
    (if 51 = n then (-14909440 : ℤ) else 0) +
    (if 52 = n then (4379648 : ℤ) else 0) +
    (if 53 = n then (6150144 : ℤ) else 0) +
    (if 54 = n then (-2306304 : ℤ) else 0) +
    (if 55 = n then (-1537536 : ℤ) else 0) +
    (if 56 = n then (658944 : ℤ) else 0) +
    (if 57 = n then (219648 : ℤ) else 0) +
    (if 58 = n then (-101904 : ℤ) else 0) +
    (if 59 = n then (-15840 : ℤ) else 0) +
    (if 60 = n then (7700 : ℤ) else 0) +
    (if 61 = n then (440 : ℤ) else 0) +
    (if 62 = n then (-219 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_25 (n : ℕ) :
    fixedRowDData_25.coeff n = fixedRowDCoeff_25 n := by
  simp only [fixedRowDData_25, fixedRowDCoeff_25, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_25 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_25 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_25, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_25 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_20 (k.val + 2) - 2 * fixedReversedUCoeff_20 (k.val + 1) + fixedReversedUCoeff_20 k.val) = fixedRowDCoeff_25 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_25 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_20 = fixedRowDData_25 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_20, fixed_rowD_typed_coeff_25]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_20, fixed_rowD_typed_coeff_25]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_20, fixed_rowD_typed_coeff_25]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_25 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_20 _ (by omega),
              fixed_reversedU_typed_tail_20 _ (by omega), fixed_reversedU_typed_tail_20 _ hn',
              fixed_rowD_typed_tail_25 _ (by omega)]
            decide

theorem fixed_rowD_typed_25 : rowD 1 25 = fixedRowDData_25 := by
  calc
    rowD 1 25 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_20 :=
      fixedTyped_rowD_of_parameters 1 25 2 63 20 (1)
        fixedChebyshevUData_20 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_20
    _ = fixedRowDData_25 := by
      rw [fixed_reversedU_typed_data_20, fixed_rowD_typed_factor_25]

end InternalCatalan

end

end

end OAI
