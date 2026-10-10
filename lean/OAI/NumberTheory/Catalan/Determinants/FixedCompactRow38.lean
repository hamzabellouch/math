import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT32To39
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU32To39

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_38 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 28 (8589934592 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-17179869184 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-64424509440 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (146028888064 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (209916526592 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-565861941248 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-378762428416 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (1323386798080 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (380473704448 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-2084334206976 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-125778788352 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (2335891783680 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-208561766400 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-1918768250880 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (373093826560 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (1172580597760 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-318513479680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-535553638400 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (176732700672 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (182088237056 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-68283088896 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-45522059264 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (18667642880 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (8186773504 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-3581713408 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1023346688 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (469502464 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (84341760 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-40062336 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-4217088 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (2053056 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (110976 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-54910 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-1156 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (577 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_38 (n : ℕ) : ℤ :=
    (if 28 = n then (8589934592 : ℤ) else 0) +
    (if 29 = n then (-17179869184 : ℤ) else 0) +
    (if 30 = n then (-64424509440 : ℤ) else 0) +
    (if 31 = n then (146028888064 : ℤ) else 0) +
    (if 32 = n then (209916526592 : ℤ) else 0) +
    (if 33 = n then (-565861941248 : ℤ) else 0) +
    (if 34 = n then (-378762428416 : ℤ) else 0) +
    (if 35 = n then (1323386798080 : ℤ) else 0) +
    (if 36 = n then (380473704448 : ℤ) else 0) +
    (if 37 = n then (-2084334206976 : ℤ) else 0) +
    (if 38 = n then (-125778788352 : ℤ) else 0) +
    (if 39 = n then (2335891783680 : ℤ) else 0) +
    (if 40 = n then (-208561766400 : ℤ) else 0) +
    (if 41 = n then (-1918768250880 : ℤ) else 0) +
    (if 42 = n then (373093826560 : ℤ) else 0) +
    (if 43 = n then (1172580597760 : ℤ) else 0) +
    (if 44 = n then (-318513479680 : ℤ) else 0) +
    (if 45 = n then (-535553638400 : ℤ) else 0) +
    (if 46 = n then (176732700672 : ℤ) else 0) +
    (if 47 = n then (182088237056 : ℤ) else 0) +
    (if 48 = n then (-68283088896 : ℤ) else 0) +
    (if 49 = n then (-45522059264 : ℤ) else 0) +
    (if 50 = n then (18667642880 : ℤ) else 0) +
    (if 51 = n then (8186773504 : ℤ) else 0) +
    (if 52 = n then (-3581713408 : ℤ) else 0) +
    (if 53 = n then (-1023346688 : ℤ) else 0) +
    (if 54 = n then (469502464 : ℤ) else 0) +
    (if 55 = n then (84341760 : ℤ) else 0) +
    (if 56 = n then (-40062336 : ℤ) else 0) +
    (if 57 = n then (-4217088 : ℤ) else 0) +
    (if 58 = n then (2053056 : ℤ) else 0) +
    (if 59 = n then (110976 : ℤ) else 0) +
    (if 60 = n then (-54910 : ℤ) else 0) +
    (if 61 = n then (-1156 : ℤ) else 0) +
    (if 62 = n then (577 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_38 (n : ℕ) :
    fixedRowPData_38.coeff n = fixedRowPCoeff_38 n := by
  simp only [fixedRowPData_38, fixedRowPCoeff_38, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_38 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_38 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_38, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_38 : ∀ k : Fin 63,
    fixedReversedTCoeff_34 (k.val + 2) - 2 * fixedReversedTCoeff_34 (k.val + 1) + fixedReversedTCoeff_34 k.val = fixedRowPCoeff_38 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_38 :
    (1 - X) ^ 2 * fixedReversedTData_34 = fixedRowPData_38 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_34, fixed_rowP_typed_coeff_38]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_34, fixed_rowP_typed_coeff_38]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_34, fixed_rowP_typed_coeff_38]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_38 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_34 _ (by omega),
              fixed_reversedT_typed_tail_34 _ (by omega), fixed_reversedT_typed_tail_34 _ hn',
              fixed_rowP_typed_tail_38 _ (by omega)]
            decide

theorem fixed_rowP_typed_38 : rowP 1 38 = fixedRowPData_38 := by
  calc
    rowP 1 38 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_34 :=
      fixedTyped_rowP_of_parameters 1 38 2 63 34 fixedChebyshevTData_34
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_34
    _ = fixedRowPData_38 := by
      rw [fixed_reversedT_typed_data_34, fixed_rowP_typed_factor_38]

def fixedRowDData_38 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 29 (8589934592 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-17179869184 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-60129542144 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (137438953472 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (180925497344 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-499289948160 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-295279001600 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (1089847951360 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (252027338752 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-1593902628864 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-27481079808 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (1648864788480 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-203654430720 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-1241555927040 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (275901317120 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (689753292800 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-203112448000 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-283528396800 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (98919907328 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (85688582144 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-33472102400 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-18744377344 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (7927463936 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (2889449472 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1294232576 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-300984320 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (140569600 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (19845120 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-9550464 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-744192 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (365568 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (13056 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-6494 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-68 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (34 : ℤ)

def fixedRowDCoeff_38 (n : ℕ) : ℤ :=
    (if 29 = n then (8589934592 : ℤ) else 0) +
    (if 30 = n then (-17179869184 : ℤ) else 0) +
    (if 31 = n then (-60129542144 : ℤ) else 0) +
    (if 32 = n then (137438953472 : ℤ) else 0) +
    (if 33 = n then (180925497344 : ℤ) else 0) +
    (if 34 = n then (-499289948160 : ℤ) else 0) +
    (if 35 = n then (-295279001600 : ℤ) else 0) +
    (if 36 = n then (1089847951360 : ℤ) else 0) +
    (if 37 = n then (252027338752 : ℤ) else 0) +
    (if 38 = n then (-1593902628864 : ℤ) else 0) +
    (if 39 = n then (-27481079808 : ℤ) else 0) +
    (if 40 = n then (1648864788480 : ℤ) else 0) +
    (if 41 = n then (-203654430720 : ℤ) else 0) +
    (if 42 = n then (-1241555927040 : ℤ) else 0) +
    (if 43 = n then (275901317120 : ℤ) else 0) +
    (if 44 = n then (689753292800 : ℤ) else 0) +
    (if 45 = n then (-203112448000 : ℤ) else 0) +
    (if 46 = n then (-283528396800 : ℤ) else 0) +
    (if 47 = n then (98919907328 : ℤ) else 0) +
    (if 48 = n then (85688582144 : ℤ) else 0) +
    (if 49 = n then (-33472102400 : ℤ) else 0) +
    (if 50 = n then (-18744377344 : ℤ) else 0) +
    (if 51 = n then (7927463936 : ℤ) else 0) +
    (if 52 = n then (2889449472 : ℤ) else 0) +
    (if 53 = n then (-1294232576 : ℤ) else 0) +
    (if 54 = n then (-300984320 : ℤ) else 0) +
    (if 55 = n then (140569600 : ℤ) else 0) +
    (if 56 = n then (19845120 : ℤ) else 0) +
    (if 57 = n then (-9550464 : ℤ) else 0) +
    (if 58 = n then (-744192 : ℤ) else 0) +
    (if 59 = n then (365568 : ℤ) else 0) +
    (if 60 = n then (13056 : ℤ) else 0) +
    (if 61 = n then (-6494 : ℤ) else 0) +
    (if 62 = n then (-68 : ℤ) else 0) +
    (if 63 = n then (34 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_38 (n : ℕ) :
    fixedRowDData_38.coeff n = fixedRowDCoeff_38 n := by
  simp only [fixedRowDData_38, fixedRowDCoeff_38, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_38 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_38 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_38, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_38 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_33 (k.val + 2) - 2 * fixedReversedUCoeff_33 (k.val + 1) + fixedReversedUCoeff_33 k.val) = fixedRowDCoeff_38 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_38 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_33 = fixedRowDData_38 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_33, fixed_rowD_typed_coeff_38]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_33, fixed_rowD_typed_coeff_38]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_33, fixed_rowD_typed_coeff_38]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_38 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_33 _ (by omega),
              fixed_reversedU_typed_tail_33 _ (by omega), fixed_reversedU_typed_tail_33 _ hn',
              fixed_rowD_typed_tail_38 _ (by omega)]
            decide

theorem fixed_rowD_typed_38 : rowD 1 38 = fixedRowDData_38 := by
  calc
    rowD 1 38 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_33 :=
      fixedTyped_rowD_of_parameters 1 38 2 63 33 (1)
        fixedChebyshevUData_33 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_33
    _ = fixedRowDData_38 := by
      rw [fixed_reversedU_typed_data_33, fixed_rowD_typed_factor_38]

end InternalCatalan

end

end

end OAI
