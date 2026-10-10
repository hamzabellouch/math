import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT16To23
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU16To23

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_21 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 45 (65536 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-131072 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-212992 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (557056 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (208896 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-974848 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (34816 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (905216 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-213248 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-478720 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (167552 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (143616 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-60384 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-22848 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (10608 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (1632 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-799 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-34 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (17 : ℤ)

def fixedRowPCoeff_21 (n : ℕ) : ℤ :=
    (if 45 = n then (65536 : ℤ) else 0) +
    (if 46 = n then (-131072 : ℤ) else 0) +
    (if 47 = n then (-212992 : ℤ) else 0) +
    (if 48 = n then (557056 : ℤ) else 0) +
    (if 49 = n then (208896 : ℤ) else 0) +
    (if 50 = n then (-974848 : ℤ) else 0) +
    (if 51 = n then (34816 : ℤ) else 0) +
    (if 52 = n then (905216 : ℤ) else 0) +
    (if 53 = n then (-213248 : ℤ) else 0) +
    (if 54 = n then (-478720 : ℤ) else 0) +
    (if 55 = n then (167552 : ℤ) else 0) +
    (if 56 = n then (143616 : ℤ) else 0) +
    (if 57 = n then (-60384 : ℤ) else 0) +
    (if 58 = n then (-22848 : ℤ) else 0) +
    (if 59 = n then (10608 : ℤ) else 0) +
    (if 60 = n then (1632 : ℤ) else 0) +
    (if 61 = n then (-799 : ℤ) else 0) +
    (if 62 = n then (-34 : ℤ) else 0) +
    (if 63 = n then (17 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_21 (n : ℕ) :
    fixedRowPData_21.coeff n = fixedRowPCoeff_21 n := by
  simp only [fixedRowPData_21, fixedRowPCoeff_21, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_21 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_21 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_21, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_21 : ∀ k : Fin 63,
    fixedReversedTCoeff_17 (k.val + 2) - 2 * fixedReversedTCoeff_17 (k.val + 1) + fixedReversedTCoeff_17 k.val = fixedRowPCoeff_21 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_21 :
    (1 - X) ^ 2 * fixedReversedTData_17 = fixedRowPData_21 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_17, fixed_rowP_typed_coeff_21]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_17, fixed_rowP_typed_coeff_21]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_17, fixed_rowP_typed_coeff_21]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_21 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_17 _ (by omega),
              fixed_reversedT_typed_tail_17 _ (by omega), fixed_reversedT_typed_tail_17 _ hn',
              fixed_rowP_typed_tail_21 _ (by omega)]
            decide

theorem fixed_rowP_typed_21 : rowP 1 21 = fixedRowPData_21 := by
  calc
    rowP 1 21 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_17 :=
      fixedTyped_rowP_of_parameters 1 21 2 63 17 fixedChebyshevTData_17
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_17
    _ = fixedRowPData_21 := by
      rw [fixed_reversedT_typed_data_17, fixed_rowP_typed_factor_21]

def fixedRowDData_21 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 46 (65536 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-131072 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-180224 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (491520 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (126976 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-745472 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (79872 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (585728 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-166144 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-253440 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (97152 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (59136 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-26208 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-6720 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (3216 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (288 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-143 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_21 (n : ℕ) : ℤ :=
    (if 46 = n then (65536 : ℤ) else 0) +
    (if 47 = n then (-131072 : ℤ) else 0) +
    (if 48 = n then (-180224 : ℤ) else 0) +
    (if 49 = n then (491520 : ℤ) else 0) +
    (if 50 = n then (126976 : ℤ) else 0) +
    (if 51 = n then (-745472 : ℤ) else 0) +
    (if 52 = n then (79872 : ℤ) else 0) +
    (if 53 = n then (585728 : ℤ) else 0) +
    (if 54 = n then (-166144 : ℤ) else 0) +
    (if 55 = n then (-253440 : ℤ) else 0) +
    (if 56 = n then (97152 : ℤ) else 0) +
    (if 57 = n then (59136 : ℤ) else 0) +
    (if 58 = n then (-26208 : ℤ) else 0) +
    (if 59 = n then (-6720 : ℤ) else 0) +
    (if 60 = n then (3216 : ℤ) else 0) +
    (if 61 = n then (288 : ℤ) else 0) +
    (if 62 = n then (-143 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_21 (n : ℕ) :
    fixedRowDData_21.coeff n = fixedRowDCoeff_21 n := by
  simp only [fixedRowDData_21, fixedRowDCoeff_21, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_21 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_21 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_21, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_21 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_16 (k.val + 2) - 2 * fixedReversedUCoeff_16 (k.val + 1) + fixedReversedUCoeff_16 k.val) = fixedRowDCoeff_21 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_21 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_16 = fixedRowDData_21 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_16, fixed_rowD_typed_coeff_21]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_16, fixed_rowD_typed_coeff_21]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_16, fixed_rowD_typed_coeff_21]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_21 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_16 _ (by omega),
              fixed_reversedU_typed_tail_16 _ (by omega), fixed_reversedU_typed_tail_16 _ hn',
              fixed_rowD_typed_tail_21 _ (by omega)]
            decide

theorem fixed_rowD_typed_21 : rowD 1 21 = fixedRowDData_21 := by
  calc
    rowD 1 21 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_16 :=
      fixedTyped_rowD_of_parameters 1 21 2 63 16 (1)
        fixedChebyshevUData_16 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_16
    _ = fixedRowDData_21 := by
      rw [fixed_reversedU_typed_data_16, fixed_rowD_typed_factor_21]

end InternalCatalan

end

end

end OAI
