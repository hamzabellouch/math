import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT24To31
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU24To31

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_31 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 35 (67108864 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-134217728 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-385875968 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (905969664 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (905969664 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-2717908992 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-1028653056 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (4775215104 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (337379328 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-5449973760 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (606928896 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (4236115968 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-974979072 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-2286157824 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (714424320 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (857309184 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-318670848 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-219967488 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (91313664 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (37340160 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-16693248 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-3953664 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (1858896 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (235872 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-114660 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-6552 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (3249 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (54 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-27 : ℤ)

def fixedRowPCoeff_31 (n : ℕ) : ℤ :=
    (if 35 = n then (67108864 : ℤ) else 0) +
    (if 36 = n then (-134217728 : ℤ) else 0) +
    (if 37 = n then (-385875968 : ℤ) else 0) +
    (if 38 = n then (905969664 : ℤ) else 0) +
    (if 39 = n then (905969664 : ℤ) else 0) +
    (if 40 = n then (-2717908992 : ℤ) else 0) +
    (if 41 = n then (-1028653056 : ℤ) else 0) +
    (if 42 = n then (4775215104 : ℤ) else 0) +
    (if 43 = n then (337379328 : ℤ) else 0) +
    (if 44 = n then (-5449973760 : ℤ) else 0) +
    (if 45 = n then (606928896 : ℤ) else 0) +
    (if 46 = n then (4236115968 : ℤ) else 0) +
    (if 47 = n then (-974979072 : ℤ) else 0) +
    (if 48 = n then (-2286157824 : ℤ) else 0) +
    (if 49 = n then (714424320 : ℤ) else 0) +
    (if 50 = n then (857309184 : ℤ) else 0) +
    (if 51 = n then (-318670848 : ℤ) else 0) +
    (if 52 = n then (-219967488 : ℤ) else 0) +
    (if 53 = n then (91313664 : ℤ) else 0) +
    (if 54 = n then (37340160 : ℤ) else 0) +
    (if 55 = n then (-16693248 : ℤ) else 0) +
    (if 56 = n then (-3953664 : ℤ) else 0) +
    (if 57 = n then (1858896 : ℤ) else 0) +
    (if 58 = n then (235872 : ℤ) else 0) +
    (if 59 = n then (-114660 : ℤ) else 0) +
    (if 60 = n then (-6552 : ℤ) else 0) +
    (if 61 = n then (3249 : ℤ) else 0) +
    (if 62 = n then (54 : ℤ) else 0) +
    (if 63 = n then (-27 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_31 (n : ℕ) :
    fixedRowPData_31.coeff n = fixedRowPCoeff_31 n := by
  simp only [fixedRowPData_31, fixedRowPCoeff_31, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_31 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_31 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_31, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_31 : ∀ k : Fin 63,
    fixedReversedTCoeff_27 (k.val + 2) - 2 * fixedReversedTCoeff_27 (k.val + 1) + fixedReversedTCoeff_27 k.val = fixedRowPCoeff_31 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_31 :
    (1 - X) ^ 2 * fixedReversedTData_27 = fixedRowPData_31 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_27, fixed_rowP_typed_coeff_31]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_27, fixed_rowP_typed_coeff_31]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_27, fixed_rowP_typed_coeff_31]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_31 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_27 _ (by omega),
              fixed_reversedT_typed_tail_27 _ (by omega), fixed_reversedT_typed_tail_27 _ hn',
              fixed_rowP_typed_tail_31 _ (by omega)]
            decide

theorem fixed_rowP_typed_31 : rowP 1 31 = fixedRowPData_31 := by
  calc
    rowP 1 31 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_27 :=
      fixedTyped_rowP_of_parameters 1 31 2 63 27 fixedChebyshevTData_27
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_27
    _ = fixedRowPData_31 := by
      rw [fixed_reversedT_typed_data_27, fixed_rowP_typed_factor_31]

def fixedRowDData_31 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 36 (67108864 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-134217728 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-352321536 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (838860800 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (738197504 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-2315255808 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-699400192 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (3714056192 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (60555264 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-3835166720 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (583991296 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (2667184128 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-698548224 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-1270087680 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (428654592 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (412778496 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-161581056 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-89616384 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (38584832 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (12446720 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-5710848 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-1025024 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (490672 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (43680 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-21476 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-728 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (363 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_31 (n : ℕ) : ℤ :=
    (if 36 = n then (67108864 : ℤ) else 0) +
    (if 37 = n then (-134217728 : ℤ) else 0) +
    (if 38 = n then (-352321536 : ℤ) else 0) +
    (if 39 = n then (838860800 : ℤ) else 0) +
    (if 40 = n then (738197504 : ℤ) else 0) +
    (if 41 = n then (-2315255808 : ℤ) else 0) +
    (if 42 = n then (-699400192 : ℤ) else 0) +
    (if 43 = n then (3714056192 : ℤ) else 0) +
    (if 44 = n then (60555264 : ℤ) else 0) +
    (if 45 = n then (-3835166720 : ℤ) else 0) +
    (if 46 = n then (583991296 : ℤ) else 0) +
    (if 47 = n then (2667184128 : ℤ) else 0) +
    (if 48 = n then (-698548224 : ℤ) else 0) +
    (if 49 = n then (-1270087680 : ℤ) else 0) +
    (if 50 = n then (428654592 : ℤ) else 0) +
    (if 51 = n then (412778496 : ℤ) else 0) +
    (if 52 = n then (-161581056 : ℤ) else 0) +
    (if 53 = n then (-89616384 : ℤ) else 0) +
    (if 54 = n then (38584832 : ℤ) else 0) +
    (if 55 = n then (12446720 : ℤ) else 0) +
    (if 56 = n then (-5710848 : ℤ) else 0) +
    (if 57 = n then (-1025024 : ℤ) else 0) +
    (if 58 = n then (490672 : ℤ) else 0) +
    (if 59 = n then (43680 : ℤ) else 0) +
    (if 60 = n then (-21476 : ℤ) else 0) +
    (if 61 = n then (-728 : ℤ) else 0) +
    (if 62 = n then (363 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_31 (n : ℕ) :
    fixedRowDData_31.coeff n = fixedRowDCoeff_31 n := by
  simp only [fixedRowDData_31, fixedRowDCoeff_31, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_31 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_31 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_31, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_31 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_26 (k.val + 2) - 2 * fixedReversedUCoeff_26 (k.val + 1) + fixedReversedUCoeff_26 k.val) = fixedRowDCoeff_31 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_31 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_26 = fixedRowDData_31 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_26, fixed_rowD_typed_coeff_31]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_26, fixed_rowD_typed_coeff_31]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_26, fixed_rowD_typed_coeff_31]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_31 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_26 _ (by omega),
              fixed_reversedU_typed_tail_26 _ (by omega), fixed_reversedU_typed_tail_26 _ hn',
              fixed_rowD_typed_tail_31 _ (by omega)]
            decide

theorem fixed_rowD_typed_31 : rowD 1 31 = fixedRowDData_31 := by
  calc
    rowD 1 31 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_26 :=
      fixedTyped_rowD_of_parameters 1 31 2 63 26 (1)
        fixedChebyshevUData_26 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_26
    _ = fixedRowDData_31 := by
      rw [fixed_reversedU_typed_data_26, fixed_rowD_typed_factor_31]

end InternalCatalan

end

end

end OAI
