import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT24To31
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU24To31

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_35 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 31 (1073741824 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-2147483648 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-7247757312 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (16642998272 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (20803747840 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-58250493952 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-31725715456 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (121701924864 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (23664263168 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-169030451200 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (2275409920 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (164479631360 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-24671944704 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-115135741952 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (28269936640 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (58595868672 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-18470436864 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-21654994944 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (7956570112 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (5741854720 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-2337755136 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-1066344448 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (466525696 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (133293056 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-61384960 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-10523136 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (5025472 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (472192 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-231136 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-9920 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (4929 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (62 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-31 : ℤ)

def fixedRowPCoeff_35 (n : ℕ) : ℤ :=
    (if 31 = n then (1073741824 : ℤ) else 0) +
    (if 32 = n then (-2147483648 : ℤ) else 0) +
    (if 33 = n then (-7247757312 : ℤ) else 0) +
    (if 34 = n then (16642998272 : ℤ) else 0) +
    (if 35 = n then (20803747840 : ℤ) else 0) +
    (if 36 = n then (-58250493952 : ℤ) else 0) +
    (if 37 = n then (-31725715456 : ℤ) else 0) +
    (if 38 = n then (121701924864 : ℤ) else 0) +
    (if 39 = n then (23664263168 : ℤ) else 0) +
    (if 40 = n then (-169030451200 : ℤ) else 0) +
    (if 41 = n then (2275409920 : ℤ) else 0) +
    (if 42 = n then (164479631360 : ℤ) else 0) +
    (if 43 = n then (-24671944704 : ℤ) else 0) +
    (if 44 = n then (-115135741952 : ℤ) else 0) +
    (if 45 = n then (28269936640 : ℤ) else 0) +
    (if 46 = n then (58595868672 : ℤ) else 0) +
    (if 47 = n then (-18470436864 : ℤ) else 0) +
    (if 48 = n then (-21654994944 : ℤ) else 0) +
    (if 49 = n then (7956570112 : ℤ) else 0) +
    (if 50 = n then (5741854720 : ℤ) else 0) +
    (if 51 = n then (-2337755136 : ℤ) else 0) +
    (if 52 = n then (-1066344448 : ℤ) else 0) +
    (if 53 = n then (466525696 : ℤ) else 0) +
    (if 54 = n then (133293056 : ℤ) else 0) +
    (if 55 = n then (-61384960 : ℤ) else 0) +
    (if 56 = n then (-10523136 : ℤ) else 0) +
    (if 57 = n then (5025472 : ℤ) else 0) +
    (if 58 = n then (472192 : ℤ) else 0) +
    (if 59 = n then (-231136 : ℤ) else 0) +
    (if 60 = n then (-9920 : ℤ) else 0) +
    (if 61 = n then (4929 : ℤ) else 0) +
    (if 62 = n then (62 : ℤ) else 0) +
    (if 63 = n then (-31 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_35 (n : ℕ) :
    fixedRowPData_35.coeff n = fixedRowPCoeff_35 n := by
  simp only [fixedRowPData_35, fixedRowPCoeff_35, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_35 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_35 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_35, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_35 : ∀ k : Fin 63,
    fixedReversedTCoeff_31 (k.val + 2) - 2 * fixedReversedTCoeff_31 (k.val + 1) + fixedReversedTCoeff_31 k.val = fixedRowPCoeff_35 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_35 :
    (1 - X) ^ 2 * fixedReversedTData_31 = fixedRowPData_35 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_31, fixed_rowP_typed_coeff_35]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_31, fixed_rowP_typed_coeff_35]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_31, fixed_rowP_typed_coeff_35]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_35 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_31 _ (by omega),
              fixed_reversedT_typed_tail_31 _ (by omega), fixed_reversedT_typed_tail_31 _ hn',
              fixed_rowP_typed_tail_35 _ (by omega)]
            decide

theorem fixed_rowP_typed_35 : rowP 1 35 = fixedRowPData_35 := by
  calc
    rowP 1 35 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_31 :=
      fixedTyped_rowP_of_parameters 1 35 2 63 31 fixedChebyshevTData_31
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_31
    _ = fixedRowPData_35 := by
      rw [fixed_reversedT_typed_data_31, fixed_rowP_typed_factor_35]

def fixedRowDData_35 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 32 (1073741824 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-2147483648 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-6710886400 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (15569256448 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (17582522368 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-50734301184 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-23706206208 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (98146713600 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (13631488000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-125409689600 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (6994001920 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (111421685760 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-20427309056 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-70567067648 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (19216924672 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (32133218304 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-10827497472 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-10478223360 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (4035174400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (2407874560 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-1014747136 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-378380288 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (169841152 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (38697984 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-18160896 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-2376192 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (1150016 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (76160 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-37600 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-960 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (479 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_35 (n : ℕ) : ℤ :=
    (if 32 = n then (1073741824 : ℤ) else 0) +
    (if 33 = n then (-2147483648 : ℤ) else 0) +
    (if 34 = n then (-6710886400 : ℤ) else 0) +
    (if 35 = n then (15569256448 : ℤ) else 0) +
    (if 36 = n then (17582522368 : ℤ) else 0) +
    (if 37 = n then (-50734301184 : ℤ) else 0) +
    (if 38 = n then (-23706206208 : ℤ) else 0) +
    (if 39 = n then (98146713600 : ℤ) else 0) +
    (if 40 = n then (13631488000 : ℤ) else 0) +
    (if 41 = n then (-125409689600 : ℤ) else 0) +
    (if 42 = n then (6994001920 : ℤ) else 0) +
    (if 43 = n then (111421685760 : ℤ) else 0) +
    (if 44 = n then (-20427309056 : ℤ) else 0) +
    (if 45 = n then (-70567067648 : ℤ) else 0) +
    (if 46 = n then (19216924672 : ℤ) else 0) +
    (if 47 = n then (32133218304 : ℤ) else 0) +
    (if 48 = n then (-10827497472 : ℤ) else 0) +
    (if 49 = n then (-10478223360 : ℤ) else 0) +
    (if 50 = n then (4035174400 : ℤ) else 0) +
    (if 51 = n then (2407874560 : ℤ) else 0) +
    (if 52 = n then (-1014747136 : ℤ) else 0) +
    (if 53 = n then (-378380288 : ℤ) else 0) +
    (if 54 = n then (169841152 : ℤ) else 0) +
    (if 55 = n then (38697984 : ℤ) else 0) +
    (if 56 = n then (-18160896 : ℤ) else 0) +
    (if 57 = n then (-2376192 : ℤ) else 0) +
    (if 58 = n then (1150016 : ℤ) else 0) +
    (if 59 = n then (76160 : ℤ) else 0) +
    (if 60 = n then (-37600 : ℤ) else 0) +
    (if 61 = n then (-960 : ℤ) else 0) +
    (if 62 = n then (479 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_35 (n : ℕ) :
    fixedRowDData_35.coeff n = fixedRowDCoeff_35 n := by
  simp only [fixedRowDData_35, fixedRowDCoeff_35, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_35 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_35 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_35, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_35 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_30 (k.val + 2) - 2 * fixedReversedUCoeff_30 (k.val + 1) + fixedReversedUCoeff_30 k.val) = fixedRowDCoeff_35 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_35 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_30 = fixedRowDData_35 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_30, fixed_rowD_typed_coeff_35]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_30, fixed_rowD_typed_coeff_35]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_30, fixed_rowD_typed_coeff_35]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_35 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_30 _ (by omega),
              fixed_reversedU_typed_tail_30 _ (by omega), fixed_reversedU_typed_tail_30 _ hn',
              fixed_rowD_typed_tail_35 _ (by omega)]
            decide

theorem fixed_rowD_typed_35 : rowD 1 35 = fixedRowDData_35 := by
  calc
    rowD 1 35 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_30 :=
      fixedTyped_rowD_of_parameters 1 35 2 63 30 (1)
        fixedChebyshevUData_30 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_30
    _ = fixedRowDData_35 := by
      rw [fixed_reversedU_typed_data_30, fixed_rowD_typed_factor_35]

end InternalCatalan

end

end

end OAI
