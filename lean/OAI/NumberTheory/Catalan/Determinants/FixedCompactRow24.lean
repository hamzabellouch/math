import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT16To23
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU16To23

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_24 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 42 (524288 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-1048576 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-2097152 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (5242880 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (2949120 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-11141120 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-983040 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (13107200 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-1894400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-9318400 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (2609152 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (4100096 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-1500928 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-1098240 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (464640 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (168960 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-77880 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-13200 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (6400 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (400 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-199 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_24 (n : ℕ) : ℤ :=
    (if 42 = n then (524288 : ℤ) else 0) +
    (if 43 = n then (-1048576 : ℤ) else 0) +
    (if 44 = n then (-2097152 : ℤ) else 0) +
    (if 45 = n then (5242880 : ℤ) else 0) +
    (if 46 = n then (2949120 : ℤ) else 0) +
    (if 47 = n then (-11141120 : ℤ) else 0) +
    (if 48 = n then (-983040 : ℤ) else 0) +
    (if 49 = n then (13107200 : ℤ) else 0) +
    (if 50 = n then (-1894400 : ℤ) else 0) +
    (if 51 = n then (-9318400 : ℤ) else 0) +
    (if 52 = n then (2609152 : ℤ) else 0) +
    (if 53 = n then (4100096 : ℤ) else 0) +
    (if 54 = n then (-1500928 : ℤ) else 0) +
    (if 55 = n then (-1098240 : ℤ) else 0) +
    (if 56 = n then (464640 : ℤ) else 0) +
    (if 57 = n then (168960 : ℤ) else 0) +
    (if 58 = n then (-77880 : ℤ) else 0) +
    (if 59 = n then (-13200 : ℤ) else 0) +
    (if 60 = n then (6400 : ℤ) else 0) +
    (if 61 = n then (400 : ℤ) else 0) +
    (if 62 = n then (-199 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_24 (n : ℕ) :
    fixedRowPData_24.coeff n = fixedRowPCoeff_24 n := by
  simp only [fixedRowPData_24, fixedRowPCoeff_24, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_24 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_24 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_24, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_24 : ∀ k : Fin 63,
    fixedReversedTCoeff_20 (k.val + 2) - 2 * fixedReversedTCoeff_20 (k.val + 1) + fixedReversedTCoeff_20 k.val = fixedRowPCoeff_24 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_24 :
    (1 - X) ^ 2 * fixedReversedTData_20 = fixedRowPData_24 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_20, fixed_rowP_typed_coeff_24]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_20, fixed_rowP_typed_coeff_24]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_20, fixed_rowP_typed_coeff_24]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_24 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_20 _ (by omega),
              fixed_reversedT_typed_tail_20 _ (by omega), fixed_reversedT_typed_tail_20 _ hn',
              fixed_rowP_typed_tail_24 _ (by omega)]
            decide

theorem fixed_rowP_typed_24 : rowP 1 24 = fixedRowPData_24 := by
  calc
    rowP 1 24 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_20 :=
      fixedTyped_rowP_of_parameters 1 24 2 63 20 fixedChebyshevTData_20
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_20
    _ = fixedRowPData_24 := by
      rw [fixed_reversedT_typed_data_20, fixed_rowP_typed_factor_24]

def fixedRowDData_24 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 43 (524288 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-1048576 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-1835008 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (4718592 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (2097152 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-8912896 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-131072 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (9175040 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-1792000 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-5591040 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (1770496 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (2050048 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-805376 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-439296 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (194304 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (50688 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-24024 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-2640 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1300 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (40 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-20 : ℤ)

def fixedRowDCoeff_24 (n : ℕ) : ℤ :=
    (if 43 = n then (524288 : ℤ) else 0) +
    (if 44 = n then (-1048576 : ℤ) else 0) +
    (if 45 = n then (-1835008 : ℤ) else 0) +
    (if 46 = n then (4718592 : ℤ) else 0) +
    (if 47 = n then (2097152 : ℤ) else 0) +
    (if 48 = n then (-8912896 : ℤ) else 0) +
    (if 49 = n then (-131072 : ℤ) else 0) +
    (if 50 = n then (9175040 : ℤ) else 0) +
    (if 51 = n then (-1792000 : ℤ) else 0) +
    (if 52 = n then (-5591040 : ℤ) else 0) +
    (if 53 = n then (1770496 : ℤ) else 0) +
    (if 54 = n then (2050048 : ℤ) else 0) +
    (if 55 = n then (-805376 : ℤ) else 0) +
    (if 56 = n then (-439296 : ℤ) else 0) +
    (if 57 = n then (194304 : ℤ) else 0) +
    (if 58 = n then (50688 : ℤ) else 0) +
    (if 59 = n then (-24024 : ℤ) else 0) +
    (if 60 = n then (-2640 : ℤ) else 0) +
    (if 61 = n then (1300 : ℤ) else 0) +
    (if 62 = n then (40 : ℤ) else 0) +
    (if 63 = n then (-20 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_24 (n : ℕ) :
    fixedRowDData_24.coeff n = fixedRowDCoeff_24 n := by
  simp only [fixedRowDData_24, fixedRowDCoeff_24, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_24 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_24 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_24, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_24 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_19 (k.val + 2) - 2 * fixedReversedUCoeff_19 (k.val + 1) + fixedReversedUCoeff_19 k.val) = fixedRowDCoeff_24 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_24 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_19 = fixedRowDData_24 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_19, fixed_rowD_typed_coeff_24]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_19, fixed_rowD_typed_coeff_24]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_19, fixed_rowD_typed_coeff_24]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_24 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_19 _ (by omega),
              fixed_reversedU_typed_tail_19 _ (by omega), fixed_reversedU_typed_tail_19 _ hn',
              fixed_rowD_typed_tail_24 _ (by omega)]
            decide

theorem fixed_rowD_typed_24 : rowD 1 24 = fixedRowDData_24 := by
  calc
    rowD 1 24 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_19 :=
      fixedTyped_rowD_of_parameters 1 24 2 63 19 (1)
        fixedChebyshevUData_19 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_19
    _ = fixedRowDData_24 := by
      rw [fixed_reversedU_typed_data_19, fixed_rowD_typed_factor_24]

end InternalCatalan

end

end

end OAI
