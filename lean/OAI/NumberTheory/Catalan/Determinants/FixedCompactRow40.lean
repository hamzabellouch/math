import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT32To39
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU32To39

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_40 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 26 (34359738368 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-68719476736 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-274877906944 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (618475290624 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (966367641600 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-2551210573824 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-1919850381312 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (6390911336448 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (2234322518016 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-10859556372480 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-1191048118272 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (13241652609024 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-643691446272 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-11954269716480 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (1913860915200 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (8126547886080 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-1968148316160 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-4190251253760 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (1276043591680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (1638164070400 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-578082897920 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-481998274560 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (188417507328 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (105163259904 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-44274462720 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-16614334464 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (7390322688 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (1833689088 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-849867264 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-133954560 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (64000512 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (5953536 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-2907000 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-139536 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (69120 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1296 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-647 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_40 (n : ℕ) : ℤ :=
    (if 26 = n then (34359738368 : ℤ) else 0) +
    (if 27 = n then (-68719476736 : ℤ) else 0) +
    (if 28 = n then (-274877906944 : ℤ) else 0) +
    (if 29 = n then (618475290624 : ℤ) else 0) +
    (if 30 = n then (966367641600 : ℤ) else 0) +
    (if 31 = n then (-2551210573824 : ℤ) else 0) +
    (if 32 = n then (-1919850381312 : ℤ) else 0) +
    (if 33 = n then (6390911336448 : ℤ) else 0) +
    (if 34 = n then (2234322518016 : ℤ) else 0) +
    (if 35 = n then (-10859556372480 : ℤ) else 0) +
    (if 36 = n then (-1191048118272 : ℤ) else 0) +
    (if 37 = n then (13241652609024 : ℤ) else 0) +
    (if 38 = n then (-643691446272 : ℤ) else 0) +
    (if 39 = n then (-11954269716480 : ℤ) else 0) +
    (if 40 = n then (1913860915200 : ℤ) else 0) +
    (if 41 = n then (8126547886080 : ℤ) else 0) +
    (if 42 = n then (-1968148316160 : ℤ) else 0) +
    (if 43 = n then (-4190251253760 : ℤ) else 0) +
    (if 44 = n then (1276043591680 : ℤ) else 0) +
    (if 45 = n then (1638164070400 : ℤ) else 0) +
    (if 46 = n then (-578082897920 : ℤ) else 0) +
    (if 47 = n then (-481998274560 : ℤ) else 0) +
    (if 48 = n then (188417507328 : ℤ) else 0) +
    (if 49 = n then (105163259904 : ℤ) else 0) +
    (if 50 = n then (-44274462720 : ℤ) else 0) +
    (if 51 = n then (-16614334464 : ℤ) else 0) +
    (if 52 = n then (7390322688 : ℤ) else 0) +
    (if 53 = n then (1833689088 : ℤ) else 0) +
    (if 54 = n then (-849867264 : ℤ) else 0) +
    (if 55 = n then (-133954560 : ℤ) else 0) +
    (if 56 = n then (64000512 : ℤ) else 0) +
    (if 57 = n then (5953536 : ℤ) else 0) +
    (if 58 = n then (-2907000 : ℤ) else 0) +
    (if 59 = n then (-139536 : ℤ) else 0) +
    (if 60 = n then (69120 : ℤ) else 0) +
    (if 61 = n then (1296 : ℤ) else 0) +
    (if 62 = n then (-647 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_40 (n : ℕ) :
    fixedRowPData_40.coeff n = fixedRowPCoeff_40 n := by
  simp only [fixedRowPData_40, fixedRowPCoeff_40, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_40 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_40 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_40, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_40 : ∀ k : Fin 63,
    fixedReversedTCoeff_36 (k.val + 2) - 2 * fixedReversedTCoeff_36 (k.val + 1) + fixedReversedTCoeff_36 k.val = fixedRowPCoeff_40 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_40 :
    (1 - X) ^ 2 * fixedReversedTData_36 = fixedRowPData_40 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_36, fixed_rowP_typed_coeff_40]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_36, fixed_rowP_typed_coeff_40]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_36, fixed_rowP_typed_coeff_40]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_40 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_36 _ (by omega),
              fixed_reversedT_typed_tail_36 _ (by omega), fixed_reversedT_typed_tail_36 _ hn',
              fixed_rowP_typed_tail_40 _ (by omega)]
            decide

theorem fixed_rowP_typed_40 : rowP 1 40 = fixedRowPData_40 := by
  calc
    rowP 1 40 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_36 :=
      fixedTyped_rowP_of_parameters 1 40 2 63 36 fixedChebyshevTData_36
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_36
    _ = fixedRowPData_40 := by
      rw [fixed_reversedT_typed_data_36, fixed_rowP_typed_factor_40]

def fixedRowDData_40 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 27 (34359738368 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-68719476736 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-257698037760 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (584115552256 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (841813590016 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-2267742732288 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-1529008357376 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (5325759447040 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (1560281088000 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-8446321623040 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-558547075072 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (9563415773184 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-796951314432 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-7969513144320 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (1501644718080 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (4966223708160 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-1319153172480 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-2327917363200 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (754417664000 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (819082035200 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-302430289920 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-214221455360 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (86662316032 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (40896823296 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-17679355904 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-5538111488 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (2514376704 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (509358080 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-239795200 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-29767680 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (14387712 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (992256 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-488376 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-15504 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (7716 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (72 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-36 : ℤ)

def fixedRowDCoeff_40 (n : ℕ) : ℤ :=
    (if 27 = n then (34359738368 : ℤ) else 0) +
    (if 28 = n then (-68719476736 : ℤ) else 0) +
    (if 29 = n then (-257698037760 : ℤ) else 0) +
    (if 30 = n then (584115552256 : ℤ) else 0) +
    (if 31 = n then (841813590016 : ℤ) else 0) +
    (if 32 = n then (-2267742732288 : ℤ) else 0) +
    (if 33 = n then (-1529008357376 : ℤ) else 0) +
    (if 34 = n then (5325759447040 : ℤ) else 0) +
    (if 35 = n then (1560281088000 : ℤ) else 0) +
    (if 36 = n then (-8446321623040 : ℤ) else 0) +
    (if 37 = n then (-558547075072 : ℤ) else 0) +
    (if 38 = n then (9563415773184 : ℤ) else 0) +
    (if 39 = n then (-796951314432 : ℤ) else 0) +
    (if 40 = n then (-7969513144320 : ℤ) else 0) +
    (if 41 = n then (1501644718080 : ℤ) else 0) +
    (if 42 = n then (4966223708160 : ℤ) else 0) +
    (if 43 = n then (-1319153172480 : ℤ) else 0) +
    (if 44 = n then (-2327917363200 : ℤ) else 0) +
    (if 45 = n then (754417664000 : ℤ) else 0) +
    (if 46 = n then (819082035200 : ℤ) else 0) +
    (if 47 = n then (-302430289920 : ℤ) else 0) +
    (if 48 = n then (-214221455360 : ℤ) else 0) +
    (if 49 = n then (86662316032 : ℤ) else 0) +
    (if 50 = n then (40896823296 : ℤ) else 0) +
    (if 51 = n then (-17679355904 : ℤ) else 0) +
    (if 52 = n then (-5538111488 : ℤ) else 0) +
    (if 53 = n then (2514376704 : ℤ) else 0) +
    (if 54 = n then (509358080 : ℤ) else 0) +
    (if 55 = n then (-239795200 : ℤ) else 0) +
    (if 56 = n then (-29767680 : ℤ) else 0) +
    (if 57 = n then (14387712 : ℤ) else 0) +
    (if 58 = n then (992256 : ℤ) else 0) +
    (if 59 = n then (-488376 : ℤ) else 0) +
    (if 60 = n then (-15504 : ℤ) else 0) +
    (if 61 = n then (7716 : ℤ) else 0) +
    (if 62 = n then (72 : ℤ) else 0) +
    (if 63 = n then (-36 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_40 (n : ℕ) :
    fixedRowDData_40.coeff n = fixedRowDCoeff_40 n := by
  simp only [fixedRowDData_40, fixedRowDCoeff_40, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_40 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_40 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_40, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_40 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_35 (k.val + 2) - 2 * fixedReversedUCoeff_35 (k.val + 1) + fixedReversedUCoeff_35 k.val) = fixedRowDCoeff_40 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_40 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_35 = fixedRowDData_40 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_35, fixed_rowD_typed_coeff_40]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_35, fixed_rowD_typed_coeff_40]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_35, fixed_rowD_typed_coeff_40]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_40 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_35 _ (by omega),
              fixed_reversedU_typed_tail_35 _ (by omega), fixed_reversedU_typed_tail_35 _ hn',
              fixed_rowD_typed_tail_40 _ (by omega)]
            decide

theorem fixed_rowD_typed_40 : rowD 1 40 = fixedRowDData_40 := by
  calc
    rowD 1 40 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_35 :=
      fixedTyped_rowD_of_parameters 1 40 2 63 35 (1)
        fixedChebyshevUData_35 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_35
    _ = fixedRowDData_40 := by
      rw [fixed_reversedU_typed_data_35, fixed_rowD_typed_factor_40]

end InternalCatalan

end

end

end OAI
