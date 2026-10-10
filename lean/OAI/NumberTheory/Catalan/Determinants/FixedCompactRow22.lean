import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT16To23
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU16To23

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_22 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 44 (131072 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-262144 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-458752 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (1179648 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (516096 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-2211840 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-12288 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (2236416 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-459264 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1317888 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (430848 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (456192 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-183744 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-88704 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (40032 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (8640 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-4158 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-324 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (161 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_22 (n : ℕ) : ℤ :=
    (if 44 = n then (131072 : ℤ) else 0) +
    (if 45 = n then (-262144 : ℤ) else 0) +
    (if 46 = n then (-458752 : ℤ) else 0) +
    (if 47 = n then (1179648 : ℤ) else 0) +
    (if 48 = n then (516096 : ℤ) else 0) +
    (if 49 = n then (-2211840 : ℤ) else 0) +
    (if 50 = n then (-12288 : ℤ) else 0) +
    (if 51 = n then (2236416 : ℤ) else 0) +
    (if 52 = n then (-459264 : ℤ) else 0) +
    (if 53 = n then (-1317888 : ℤ) else 0) +
    (if 54 = n then (430848 : ℤ) else 0) +
    (if 55 = n then (456192 : ℤ) else 0) +
    (if 56 = n then (-183744 : ℤ) else 0) +
    (if 57 = n then (-88704 : ℤ) else 0) +
    (if 58 = n then (40032 : ℤ) else 0) +
    (if 59 = n then (8640 : ℤ) else 0) +
    (if 60 = n then (-4158 : ℤ) else 0) +
    (if 61 = n then (-324 : ℤ) else 0) +
    (if 62 = n then (161 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_22 (n : ℕ) :
    fixedRowPData_22.coeff n = fixedRowPCoeff_22 n := by
  simp only [fixedRowPData_22, fixedRowPCoeff_22, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_22 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_22 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_22, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_22 : ∀ k : Fin 63,
    fixedReversedTCoeff_18 (k.val + 2) - 2 * fixedReversedTCoeff_18 (k.val + 1) + fixedReversedTCoeff_18 k.val = fixedRowPCoeff_22 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_22 :
    (1 - X) ^ 2 * fixedReversedTData_18 = fixedRowPData_22 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_18, fixed_rowP_typed_coeff_22]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_18, fixed_rowP_typed_coeff_22]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_18, fixed_rowP_typed_coeff_22]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_22 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_18 _ (by omega),
              fixed_reversedT_typed_tail_18 _ (by omega), fixed_reversedT_typed_tail_18 _ hn',
              fixed_rowP_typed_tail_22 _ (by omega)]
            decide

theorem fixed_rowP_typed_22 : rowP 1 22 = fixedRowPData_22 := by
  calc
    rowP 1 22 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_18 :=
      fixedTyped_rowP_of_parameters 1 22 2 63 18 fixedChebyshevTData_18
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_18
    _ = fixedRowPData_22 := by
      rw [fixed_reversedT_typed_data_18, fixed_rowP_typed_factor_22]

def fixedRowDData_22 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 45 (131072 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-262144 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-393216 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (1048576 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (335872 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-1720320 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (114688 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (1490944 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-379392 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-732160 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (264704 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (202752 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-86592 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-29568 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (13824 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (1920 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-942 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-36 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (18 : ℤ)

def fixedRowDCoeff_22 (n : ℕ) : ℤ :=
    (if 45 = n then (131072 : ℤ) else 0) +
    (if 46 = n then (-262144 : ℤ) else 0) +
    (if 47 = n then (-393216 : ℤ) else 0) +
    (if 48 = n then (1048576 : ℤ) else 0) +
    (if 49 = n then (335872 : ℤ) else 0) +
    (if 50 = n then (-1720320 : ℤ) else 0) +
    (if 51 = n then (114688 : ℤ) else 0) +
    (if 52 = n then (1490944 : ℤ) else 0) +
    (if 53 = n then (-379392 : ℤ) else 0) +
    (if 54 = n then (-732160 : ℤ) else 0) +
    (if 55 = n then (264704 : ℤ) else 0) +
    (if 56 = n then (202752 : ℤ) else 0) +
    (if 57 = n then (-86592 : ℤ) else 0) +
    (if 58 = n then (-29568 : ℤ) else 0) +
    (if 59 = n then (13824 : ℤ) else 0) +
    (if 60 = n then (1920 : ℤ) else 0) +
    (if 61 = n then (-942 : ℤ) else 0) +
    (if 62 = n then (-36 : ℤ) else 0) +
    (if 63 = n then (18 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_22 (n : ℕ) :
    fixedRowDData_22.coeff n = fixedRowDCoeff_22 n := by
  simp only [fixedRowDData_22, fixedRowDCoeff_22, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_22 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_22 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_22, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_22 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_17 (k.val + 2) - 2 * fixedReversedUCoeff_17 (k.val + 1) + fixedReversedUCoeff_17 k.val) = fixedRowDCoeff_22 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_22 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_17 = fixedRowDData_22 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_17, fixed_rowD_typed_coeff_22]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_17, fixed_rowD_typed_coeff_22]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_17, fixed_rowD_typed_coeff_22]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_22 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_17 _ (by omega),
              fixed_reversedU_typed_tail_17 _ (by omega), fixed_reversedU_typed_tail_17 _ hn',
              fixed_rowD_typed_tail_22 _ (by omega)]
            decide

theorem fixed_rowD_typed_22 : rowD 1 22 = fixedRowDData_22 := by
  calc
    rowD 1 22 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_17 :=
      fixedTyped_rowD_of_parameters 1 22 2 63 17 (1)
        fixedChebyshevUData_17 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_17
    _ = fixedRowDData_22 := by
      rw [fixed_reversedU_typed_data_17, fixed_rowD_typed_factor_22]

end InternalCatalan

end

end

end OAI
