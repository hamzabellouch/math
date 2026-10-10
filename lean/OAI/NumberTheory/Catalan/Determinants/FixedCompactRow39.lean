import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT32To39
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU32To39

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_39 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 27 (17179869184 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-34359738368 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-133143986176 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (300647710720 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (450971566080 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-1202590842880 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-854966927360 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (2912524697600 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (927780044800 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-4768084787200 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-405287206912 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (5578659201024 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-384735117312 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-4809188966400 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (852649574400 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (3103889817600 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-797527244800 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-1508835328000 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (478765056000 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (551305216000 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-200675098624 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-149955018752 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (60067209216 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (29820600320 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-12803409920 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-4213780480 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (1904304640 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (405171200 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-190182400 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-24806400 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (11969088 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (868224 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-426972 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-14280 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (7105 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (70 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-35 : ℤ)

def fixedRowPCoeff_39 (n : ℕ) : ℤ :=
    (if 27 = n then (17179869184 : ℤ) else 0) +
    (if 28 = n then (-34359738368 : ℤ) else 0) +
    (if 29 = n then (-133143986176 : ℤ) else 0) +
    (if 30 = n then (300647710720 : ℤ) else 0) +
    (if 31 = n then (450971566080 : ℤ) else 0) +
    (if 32 = n then (-1202590842880 : ℤ) else 0) +
    (if 33 = n then (-854966927360 : ℤ) else 0) +
    (if 34 = n then (2912524697600 : ℤ) else 0) +
    (if 35 = n then (927780044800 : ℤ) else 0) +
    (if 36 = n then (-4768084787200 : ℤ) else 0) +
    (if 37 = n then (-405287206912 : ℤ) else 0) +
    (if 38 = n then (5578659201024 : ℤ) else 0) +
    (if 39 = n then (-384735117312 : ℤ) else 0) +
    (if 40 = n then (-4809188966400 : ℤ) else 0) +
    (if 41 = n then (852649574400 : ℤ) else 0) +
    (if 42 = n then (3103889817600 : ℤ) else 0) +
    (if 43 = n then (-797527244800 : ℤ) else 0) +
    (if 44 = n then (-1508835328000 : ℤ) else 0) +
    (if 45 = n then (478765056000 : ℤ) else 0) +
    (if 46 = n then (551305216000 : ℤ) else 0) +
    (if 47 = n then (-200675098624 : ℤ) else 0) +
    (if 48 = n then (-149955018752 : ℤ) else 0) +
    (if 49 = n then (60067209216 : ℤ) else 0) +
    (if 50 = n then (29820600320 : ℤ) else 0) +
    (if 51 = n then (-12803409920 : ℤ) else 0) +
    (if 52 = n then (-4213780480 : ℤ) else 0) +
    (if 53 = n then (1904304640 : ℤ) else 0) +
    (if 54 = n then (405171200 : ℤ) else 0) +
    (if 55 = n then (-190182400 : ℤ) else 0) +
    (if 56 = n then (-24806400 : ℤ) else 0) +
    (if 57 = n then (11969088 : ℤ) else 0) +
    (if 58 = n then (868224 : ℤ) else 0) +
    (if 59 = n then (-426972 : ℤ) else 0) +
    (if 60 = n then (-14280 : ℤ) else 0) +
    (if 61 = n then (7105 : ℤ) else 0) +
    (if 62 = n then (70 : ℤ) else 0) +
    (if 63 = n then (-35 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_39 (n : ℕ) :
    fixedRowPData_39.coeff n = fixedRowPCoeff_39 n := by
  simp only [fixedRowPData_39, fixedRowPCoeff_39, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_39 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_39 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_39, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_39 : ∀ k : Fin 63,
    fixedReversedTCoeff_35 (k.val + 2) - 2 * fixedReversedTCoeff_35 (k.val + 1) + fixedReversedTCoeff_35 k.val = fixedRowPCoeff_39 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_39 :
    (1 - X) ^ 2 * fixedReversedTData_35 = fixedRowPData_39 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_35, fixed_rowP_typed_coeff_39]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_35, fixed_rowP_typed_coeff_39]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_35, fixed_rowP_typed_coeff_39]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_39 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_35 _ (by omega),
              fixed_reversedT_typed_tail_35 _ (by omega), fixed_reversedT_typed_tail_35 _ hn',
              fixed_rowP_typed_tail_39 _ (by omega)]
            decide

theorem fixed_rowP_typed_39 : rowP 1 39 = fixedRowPData_39 := by
  calc
    rowP 1 39 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_35 :=
      fixedTyped_rowP_of_parameters 1 39 2 63 35 fixedChebyshevTData_35
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_35
    _ = fixedRowPData_39 := by
      rw [fixed_reversedT_typed_data_35, fixed_rowP_typed_factor_39]

def fixedRowDData_39 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 28 (17179869184 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-34359738368 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-124554051584 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (283467841536 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (390842023936 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-1065151889408 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-674041430016 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (2413234749440 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (632501043200 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-3678236835840 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-153259868160 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (3984756572160 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-412216197120 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-3160324177920 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (648995143680 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (1862333890560 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-521625927680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-819082035200 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (275652608000 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (267776819200 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-101755191296 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-64266436608 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (26595106816 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (11076222976 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-4875945984 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1324331008 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (610072064 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (104186880 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-49612800 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-4961280 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (2418624 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (124032 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-61404 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-1224 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (611 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_39 (n : ℕ) : ℤ :=
    (if 28 = n then (17179869184 : ℤ) else 0) +
    (if 29 = n then (-34359738368 : ℤ) else 0) +
    (if 30 = n then (-124554051584 : ℤ) else 0) +
    (if 31 = n then (283467841536 : ℤ) else 0) +
    (if 32 = n then (390842023936 : ℤ) else 0) +
    (if 33 = n then (-1065151889408 : ℤ) else 0) +
    (if 34 = n then (-674041430016 : ℤ) else 0) +
    (if 35 = n then (2413234749440 : ℤ) else 0) +
    (if 36 = n then (632501043200 : ℤ) else 0) +
    (if 37 = n then (-3678236835840 : ℤ) else 0) +
    (if 38 = n then (-153259868160 : ℤ) else 0) +
    (if 39 = n then (3984756572160 : ℤ) else 0) +
    (if 40 = n then (-412216197120 : ℤ) else 0) +
    (if 41 = n then (-3160324177920 : ℤ) else 0) +
    (if 42 = n then (648995143680 : ℤ) else 0) +
    (if 43 = n then (1862333890560 : ℤ) else 0) +
    (if 44 = n then (-521625927680 : ℤ) else 0) +
    (if 45 = n then (-819082035200 : ℤ) else 0) +
    (if 46 = n then (275652608000 : ℤ) else 0) +
    (if 47 = n then (267776819200 : ℤ) else 0) +
    (if 48 = n then (-101755191296 : ℤ) else 0) +
    (if 49 = n then (-64266436608 : ℤ) else 0) +
    (if 50 = n then (26595106816 : ℤ) else 0) +
    (if 51 = n then (11076222976 : ℤ) else 0) +
    (if 52 = n then (-4875945984 : ℤ) else 0) +
    (if 53 = n then (-1324331008 : ℤ) else 0) +
    (if 54 = n then (610072064 : ℤ) else 0) +
    (if 55 = n then (104186880 : ℤ) else 0) +
    (if 56 = n then (-49612800 : ℤ) else 0) +
    (if 57 = n then (-4961280 : ℤ) else 0) +
    (if 58 = n then (2418624 : ℤ) else 0) +
    (if 59 = n then (124032 : ℤ) else 0) +
    (if 60 = n then (-61404 : ℤ) else 0) +
    (if 61 = n then (-1224 : ℤ) else 0) +
    (if 62 = n then (611 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_39 (n : ℕ) :
    fixedRowDData_39.coeff n = fixedRowDCoeff_39 n := by
  simp only [fixedRowDData_39, fixedRowDCoeff_39, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_39 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_39 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_39, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_39 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_34 (k.val + 2) - 2 * fixedReversedUCoeff_34 (k.val + 1) + fixedReversedUCoeff_34 k.val) = fixedRowDCoeff_39 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_39 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_34 = fixedRowDData_39 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_34, fixed_rowD_typed_coeff_39]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_34, fixed_rowD_typed_coeff_39]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_34, fixed_rowD_typed_coeff_39]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_39 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_34 _ (by omega),
              fixed_reversedU_typed_tail_34 _ (by omega), fixed_reversedU_typed_tail_34 _ hn',
              fixed_rowD_typed_tail_39 _ (by omega)]
            decide

theorem fixed_rowD_typed_39 : rowD 1 39 = fixedRowDData_39 := by
  calc
    rowD 1 39 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_34 :=
      fixedTyped_rowD_of_parameters 1 39 2 63 34 (1)
        fixedChebyshevUData_34 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_34
    _ = fixedRowDData_39 := by
      rw [fixed_reversedU_typed_data_34, fixed_rowD_typed_factor_39]

end InternalCatalan

end

end

end OAI
