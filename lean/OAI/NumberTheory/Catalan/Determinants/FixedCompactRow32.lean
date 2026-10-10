import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT24To31
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU24To31

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_32 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 34 (134217728 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-268435456 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-805306368 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (1879048192 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (1996488704 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-5872025600 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-2466250752 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (10804527104 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (1097334784 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-12999196672 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (1130364928 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (10738466816 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-2257518592 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-6223429632 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (1841627136 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (2540175360 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-908906496 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-722362368 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (291479552 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (139403264 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-60988928 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-17425408 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (8060416 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (1304576 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-626808 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-50960 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (25088 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (784 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-391 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_32 (n : ℕ) : ℤ :=
    (if 34 = n then (134217728 : ℤ) else 0) +
    (if 35 = n then (-268435456 : ℤ) else 0) +
    (if 36 = n then (-805306368 : ℤ) else 0) +
    (if 37 = n then (1879048192 : ℤ) else 0) +
    (if 38 = n then (1996488704 : ℤ) else 0) +
    (if 39 = n then (-5872025600 : ℤ) else 0) +
    (if 40 = n then (-2466250752 : ℤ) else 0) +
    (if 41 = n then (10804527104 : ℤ) else 0) +
    (if 42 = n then (1097334784 : ℤ) else 0) +
    (if 43 = n then (-12999196672 : ℤ) else 0) +
    (if 44 = n then (1130364928 : ℤ) else 0) +
    (if 45 = n then (10738466816 : ℤ) else 0) +
    (if 46 = n then (-2257518592 : ℤ) else 0) +
    (if 47 = n then (-6223429632 : ℤ) else 0) +
    (if 48 = n then (1841627136 : ℤ) else 0) +
    (if 49 = n then (2540175360 : ℤ) else 0) +
    (if 50 = n then (-908906496 : ℤ) else 0) +
    (if 51 = n then (-722362368 : ℤ) else 0) +
    (if 52 = n then (291479552 : ℤ) else 0) +
    (if 53 = n then (139403264 : ℤ) else 0) +
    (if 54 = n then (-60988928 : ℤ) else 0) +
    (if 55 = n then (-17425408 : ℤ) else 0) +
    (if 56 = n then (8060416 : ℤ) else 0) +
    (if 57 = n then (1304576 : ℤ) else 0) +
    (if 58 = n then (-626808 : ℤ) else 0) +
    (if 59 = n then (-50960 : ℤ) else 0) +
    (if 60 = n then (25088 : ℤ) else 0) +
    (if 61 = n then (784 : ℤ) else 0) +
    (if 62 = n then (-391 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_32 (n : ℕ) :
    fixedRowPData_32.coeff n = fixedRowPCoeff_32 n := by
  simp only [fixedRowPData_32, fixedRowPCoeff_32, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_32 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_32 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_32, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_32 : ∀ k : Fin 63,
    fixedReversedTCoeff_28 (k.val + 2) - 2 * fixedReversedTCoeff_28 (k.val + 1) + fixedReversedTCoeff_28 k.val = fixedRowPCoeff_32 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_32 :
    (1 - X) ^ 2 * fixedReversedTData_28 = fixedRowPData_32 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_28, fixed_rowP_typed_coeff_32]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_28, fixed_rowP_typed_coeff_32]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_28, fixed_rowP_typed_coeff_32]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_32 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_28 _ (by omega),
              fixed_reversedT_typed_tail_28 _ (by omega), fixed_reversedT_typed_tail_28 _ hn',
              fixed_rowP_typed_tail_32 _ (by omega)]
            decide

theorem fixed_rowP_typed_32 : rowP 1 32 = fixedRowPData_32 := by
  calc
    rowP 1 32 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_28 :=
      fixedTyped_rowP_of_parameters 1 32 2 63 28 fixedChebyshevTData_28
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_28
    _ = fixedRowPData_32 := by
      rw [fixed_reversedT_typed_data_28, fixed_rowP_typed_factor_32]

def fixedRowDData_32 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 35 (134217728 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-268435456 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-738197504 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (1744830464 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (1644167168 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-5033164800 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-1728053248 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (8489271296 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (397934592 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-9285140480 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (1190920192 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (6903300096 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-1673527296 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-3556245504 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (1143078912 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (1270087680 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-480251904 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-309583872 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (129898496 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (49786880 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-22404096 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-4978688 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (2349568 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (279552 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-136136 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-7280 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (3612 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (56 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-28 : ℤ)

def fixedRowDCoeff_32 (n : ℕ) : ℤ :=
    (if 35 = n then (134217728 : ℤ) else 0) +
    (if 36 = n then (-268435456 : ℤ) else 0) +
    (if 37 = n then (-738197504 : ℤ) else 0) +
    (if 38 = n then (1744830464 : ℤ) else 0) +
    (if 39 = n then (1644167168 : ℤ) else 0) +
    (if 40 = n then (-5033164800 : ℤ) else 0) +
    (if 41 = n then (-1728053248 : ℤ) else 0) +
    (if 42 = n then (8489271296 : ℤ) else 0) +
    (if 43 = n then (397934592 : ℤ) else 0) +
    (if 44 = n then (-9285140480 : ℤ) else 0) +
    (if 45 = n then (1190920192 : ℤ) else 0) +
    (if 46 = n then (6903300096 : ℤ) else 0) +
    (if 47 = n then (-1673527296 : ℤ) else 0) +
    (if 48 = n then (-3556245504 : ℤ) else 0) +
    (if 49 = n then (1143078912 : ℤ) else 0) +
    (if 50 = n then (1270087680 : ℤ) else 0) +
    (if 51 = n then (-480251904 : ℤ) else 0) +
    (if 52 = n then (-309583872 : ℤ) else 0) +
    (if 53 = n then (129898496 : ℤ) else 0) +
    (if 54 = n then (49786880 : ℤ) else 0) +
    (if 55 = n then (-22404096 : ℤ) else 0) +
    (if 56 = n then (-4978688 : ℤ) else 0) +
    (if 57 = n then (2349568 : ℤ) else 0) +
    (if 58 = n then (279552 : ℤ) else 0) +
    (if 59 = n then (-136136 : ℤ) else 0) +
    (if 60 = n then (-7280 : ℤ) else 0) +
    (if 61 = n then (3612 : ℤ) else 0) +
    (if 62 = n then (56 : ℤ) else 0) +
    (if 63 = n then (-28 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_32 (n : ℕ) :
    fixedRowDData_32.coeff n = fixedRowDCoeff_32 n := by
  simp only [fixedRowDData_32, fixedRowDCoeff_32, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_32 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_32 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_32, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_32 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_27 (k.val + 2) - 2 * fixedReversedUCoeff_27 (k.val + 1) + fixedReversedUCoeff_27 k.val) = fixedRowDCoeff_32 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_32 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_27 = fixedRowDData_32 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_27, fixed_rowD_typed_coeff_32]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_27, fixed_rowD_typed_coeff_32]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_27, fixed_rowD_typed_coeff_32]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_32 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_27 _ (by omega),
              fixed_reversedU_typed_tail_27 _ (by omega), fixed_reversedU_typed_tail_27 _ hn',
              fixed_rowD_typed_tail_32 _ (by omega)]
            decide

theorem fixed_rowD_typed_32 : rowD 1 32 = fixedRowDData_32 := by
  calc
    rowD 1 32 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_27 :=
      fixedTyped_rowD_of_parameters 1 32 2 63 27 (1)
        fixedChebyshevUData_27 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_27
    _ = fixedRowDData_32 := by
      rw [fixed_reversedU_typed_data_27, fixed_rowD_typed_factor_32]

end InternalCatalan

end

end

end OAI
