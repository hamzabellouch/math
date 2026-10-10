import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT16To23
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU16To23

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_23 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 43 (262144 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-524288 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-983040 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (2490368 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (1245184 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-4980736 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-233472 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (5447680 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-953344 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-3540992 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (1074944 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (1391104 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-535040 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-321024 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (140448 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (40128 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-18924 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-2280 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1121 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (38 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-19 : ℤ)

def fixedRowPCoeff_23 (n : ℕ) : ℤ :=
    (if 43 = n then (262144 : ℤ) else 0) +
    (if 44 = n then (-524288 : ℤ) else 0) +
    (if 45 = n then (-983040 : ℤ) else 0) +
    (if 46 = n then (2490368 : ℤ) else 0) +
    (if 47 = n then (1245184 : ℤ) else 0) +
    (if 48 = n then (-4980736 : ℤ) else 0) +
    (if 49 = n then (-233472 : ℤ) else 0) +
    (if 50 = n then (5447680 : ℤ) else 0) +
    (if 51 = n then (-953344 : ℤ) else 0) +
    (if 52 = n then (-3540992 : ℤ) else 0) +
    (if 53 = n then (1074944 : ℤ) else 0) +
    (if 54 = n then (1391104 : ℤ) else 0) +
    (if 55 = n then (-535040 : ℤ) else 0) +
    (if 56 = n then (-321024 : ℤ) else 0) +
    (if 57 = n then (140448 : ℤ) else 0) +
    (if 58 = n then (40128 : ℤ) else 0) +
    (if 59 = n then (-18924 : ℤ) else 0) +
    (if 60 = n then (-2280 : ℤ) else 0) +
    (if 61 = n then (1121 : ℤ) else 0) +
    (if 62 = n then (38 : ℤ) else 0) +
    (if 63 = n then (-19 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_23 (n : ℕ) :
    fixedRowPData_23.coeff n = fixedRowPCoeff_23 n := by
  simp only [fixedRowPData_23, fixedRowPCoeff_23, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_23 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_23 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_23, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_23 : ∀ k : Fin 63,
    fixedReversedTCoeff_19 (k.val + 2) - 2 * fixedReversedTCoeff_19 (k.val + 1) + fixedReversedTCoeff_19 k.val = fixedRowPCoeff_23 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_23 :
    (1 - X) ^ 2 * fixedReversedTData_19 = fixedRowPData_23 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_19, fixed_rowP_typed_coeff_23]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_19, fixed_rowP_typed_coeff_23]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_19, fixed_rowP_typed_coeff_23]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_23 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_19 _ (by omega),
              fixed_reversedT_typed_tail_19 _ (by omega), fixed_reversedT_typed_tail_19 _ hn',
              fixed_rowP_typed_tail_23 _ (by omega)]
            decide

theorem fixed_rowP_typed_23 : rowP 1 23 = fixedRowPData_23 := by
  calc
    rowP 1 23 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_19 :=
      fixedTyped_rowP_of_parameters 1 23 2 63 19 fixedChebyshevTData_19
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_19
    _ = fixedRowPData_23 := by
      rw [fixed_reversedT_typed_data_19, fixed_rowP_typed_factor_23]

def fixedRowDData_23 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 44 (262144 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-524288 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-851968 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (2228224 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (851968 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-3932160 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (102400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (3727360 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-838656 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-2050048 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (695552 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (658944 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-270336 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-118272 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (53856 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (10560 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-5100 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-360 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (179 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_23 (n : ℕ) : ℤ :=
    (if 44 = n then (262144 : ℤ) else 0) +
    (if 45 = n then (-524288 : ℤ) else 0) +
    (if 46 = n then (-851968 : ℤ) else 0) +
    (if 47 = n then (2228224 : ℤ) else 0) +
    (if 48 = n then (851968 : ℤ) else 0) +
    (if 49 = n then (-3932160 : ℤ) else 0) +
    (if 50 = n then (102400 : ℤ) else 0) +
    (if 51 = n then (3727360 : ℤ) else 0) +
    (if 52 = n then (-838656 : ℤ) else 0) +
    (if 53 = n then (-2050048 : ℤ) else 0) +
    (if 54 = n then (695552 : ℤ) else 0) +
    (if 55 = n then (658944 : ℤ) else 0) +
    (if 56 = n then (-270336 : ℤ) else 0) +
    (if 57 = n then (-118272 : ℤ) else 0) +
    (if 58 = n then (53856 : ℤ) else 0) +
    (if 59 = n then (10560 : ℤ) else 0) +
    (if 60 = n then (-5100 : ℤ) else 0) +
    (if 61 = n then (-360 : ℤ) else 0) +
    (if 62 = n then (179 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_23 (n : ℕ) :
    fixedRowDData_23.coeff n = fixedRowDCoeff_23 n := by
  simp only [fixedRowDData_23, fixedRowDCoeff_23, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_23 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_23 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_23, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_23 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_18 (k.val + 2) - 2 * fixedReversedUCoeff_18 (k.val + 1) + fixedReversedUCoeff_18 k.val) = fixedRowDCoeff_23 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_23 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_18 = fixedRowDData_23 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_18, fixed_rowD_typed_coeff_23]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_18, fixed_rowD_typed_coeff_23]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_18, fixed_rowD_typed_coeff_23]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_23 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_18 _ (by omega),
              fixed_reversedU_typed_tail_18 _ (by omega), fixed_reversedU_typed_tail_18 _ hn',
              fixed_rowD_typed_tail_23 _ (by omega)]
            decide

theorem fixed_rowD_typed_23 : rowD 1 23 = fixedRowDData_23 := by
  calc
    rowD 1 23 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_18 :=
      fixedTyped_rowD_of_parameters 1 23 2 63 18 (1)
        fixedChebyshevUData_18 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_18
    _ = fixedRowDData_23 := by
      rw [fixed_reversedU_typed_data_18, fixed_rowD_typed_factor_23]

end InternalCatalan

end

end

end OAI
