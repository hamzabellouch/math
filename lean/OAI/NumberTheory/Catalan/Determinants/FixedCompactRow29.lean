import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT24To31
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU24To31

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_29 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 37 (16777216 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-33554432 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-88080384 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (209715200 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (183500800 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-576716800 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-170393600 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (917504000 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (8192000 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-933888000 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (149422080 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (635043840 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-171294720 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-292454400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (100966400 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (90521600 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-36108800 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-18304000 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (8008000 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (2288000 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-1063920 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-160160 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (77480 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (5200 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-2575 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-50 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (25 : ℤ)

def fixedRowPCoeff_29 (n : ℕ) : ℤ :=
    (if 37 = n then (16777216 : ℤ) else 0) +
    (if 38 = n then (-33554432 : ℤ) else 0) +
    (if 39 = n then (-88080384 : ℤ) else 0) +
    (if 40 = n then (209715200 : ℤ) else 0) +
    (if 41 = n then (183500800 : ℤ) else 0) +
    (if 42 = n then (-576716800 : ℤ) else 0) +
    (if 43 = n then (-170393600 : ℤ) else 0) +
    (if 44 = n then (917504000 : ℤ) else 0) +
    (if 45 = n then (8192000 : ℤ) else 0) +
    (if 46 = n then (-933888000 : ℤ) else 0) +
    (if 47 = n then (149422080 : ℤ) else 0) +
    (if 48 = n then (635043840 : ℤ) else 0) +
    (if 49 = n then (-171294720 : ℤ) else 0) +
    (if 50 = n then (-292454400 : ℤ) else 0) +
    (if 51 = n then (100966400 : ℤ) else 0) +
    (if 52 = n then (90521600 : ℤ) else 0) +
    (if 53 = n then (-36108800 : ℤ) else 0) +
    (if 54 = n then (-18304000 : ℤ) else 0) +
    (if 55 = n then (8008000 : ℤ) else 0) +
    (if 56 = n then (2288000 : ℤ) else 0) +
    (if 57 = n then (-1063920 : ℤ) else 0) +
    (if 58 = n then (-160160 : ℤ) else 0) +
    (if 59 = n then (77480 : ℤ) else 0) +
    (if 60 = n then (5200 : ℤ) else 0) +
    (if 61 = n then (-2575 : ℤ) else 0) +
    (if 62 = n then (-50 : ℤ) else 0) +
    (if 63 = n then (25 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_29 (n : ℕ) :
    fixedRowPData_29.coeff n = fixedRowPCoeff_29 n := by
  simp only [fixedRowPData_29, fixedRowPCoeff_29, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_29 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_29 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_29, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_29 : ∀ k : Fin 63,
    fixedReversedTCoeff_25 (k.val + 2) - 2 * fixedReversedTCoeff_25 (k.val + 1) + fixedReversedTCoeff_25 k.val = fixedRowPCoeff_29 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_29 :
    (1 - X) ^ 2 * fixedReversedTData_25 = fixedRowPData_29 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_25, fixed_rowP_typed_coeff_29]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_25, fixed_rowP_typed_coeff_29]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_25, fixed_rowP_typed_coeff_29]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_29 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_25 _ (by omega),
              fixed_reversedT_typed_tail_25 _ (by omega), fixed_reversedT_typed_tail_25 _ hn',
              fixed_rowP_typed_tail_29 _ (by omega)]
            decide

theorem fixed_rowP_typed_29 : rowP 1 29 = fixedRowPData_29 := by
  calc
    rowP 1 29 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_25 :=
      fixedTyped_rowP_of_parameters 1 29 2 63 25 fixedChebyshevTData_25
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_25
    _ = fixedRowPData_29 := by
      rw [fixed_reversedT_typed_data_25, fixed_rowP_typed_factor_29]

def fixedRowDData_29 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 38 (16777216 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-33554432 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-79691776 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (192937984 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (145752064 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-484442112 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-106430464 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (697303040 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-31129600 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-635043840 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (127008768 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (381026304 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-114475008 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-152076288 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (56123392 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (39829504 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-16620032 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-6589440 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (2974400 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (640640 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-304304 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-32032 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (15704 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (624 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-311 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_29 (n : ℕ) : ℤ :=
    (if 38 = n then (16777216 : ℤ) else 0) +
    (if 39 = n then (-33554432 : ℤ) else 0) +
    (if 40 = n then (-79691776 : ℤ) else 0) +
    (if 41 = n then (192937984 : ℤ) else 0) +
    (if 42 = n then (145752064 : ℤ) else 0) +
    (if 43 = n then (-484442112 : ℤ) else 0) +
    (if 44 = n then (-106430464 : ℤ) else 0) +
    (if 45 = n then (697303040 : ℤ) else 0) +
    (if 46 = n then (-31129600 : ℤ) else 0) +
    (if 47 = n then (-635043840 : ℤ) else 0) +
    (if 48 = n then (127008768 : ℤ) else 0) +
    (if 49 = n then (381026304 : ℤ) else 0) +
    (if 50 = n then (-114475008 : ℤ) else 0) +
    (if 51 = n then (-152076288 : ℤ) else 0) +
    (if 52 = n then (56123392 : ℤ) else 0) +
    (if 53 = n then (39829504 : ℤ) else 0) +
    (if 54 = n then (-16620032 : ℤ) else 0) +
    (if 55 = n then (-6589440 : ℤ) else 0) +
    (if 56 = n then (2974400 : ℤ) else 0) +
    (if 57 = n then (640640 : ℤ) else 0) +
    (if 58 = n then (-304304 : ℤ) else 0) +
    (if 59 = n then (-32032 : ℤ) else 0) +
    (if 60 = n then (15704 : ℤ) else 0) +
    (if 61 = n then (624 : ℤ) else 0) +
    (if 62 = n then (-311 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_29 (n : ℕ) :
    fixedRowDData_29.coeff n = fixedRowDCoeff_29 n := by
  simp only [fixedRowDData_29, fixedRowDCoeff_29, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_29 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_29 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_29, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_29 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_24 (k.val + 2) - 2 * fixedReversedUCoeff_24 (k.val + 1) + fixedReversedUCoeff_24 k.val) = fixedRowDCoeff_29 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_29 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_24 = fixedRowDData_29 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_24, fixed_rowD_typed_coeff_29]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_24, fixed_rowD_typed_coeff_29]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_24, fixed_rowD_typed_coeff_29]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_29 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_24 _ (by omega),
              fixed_reversedU_typed_tail_24 _ (by omega), fixed_reversedU_typed_tail_24 _ hn',
              fixed_rowD_typed_tail_29 _ (by omega)]
            decide

theorem fixed_rowD_typed_29 : rowD 1 29 = fixedRowDData_29 := by
  calc
    rowD 1 29 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_24 :=
      fixedTyped_rowD_of_parameters 1 29 2 63 24 (1)
        fixedChebyshevUData_24 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_24
    _ = fixedRowDData_29 := by
      rw [fixed_reversedU_typed_data_24, fixed_rowD_typed_factor_29]

end InternalCatalan

end

end

end OAI
