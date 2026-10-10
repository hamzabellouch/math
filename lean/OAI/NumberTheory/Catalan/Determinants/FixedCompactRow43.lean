import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT32To39
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU32To39

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_43 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 23 (274877906944 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-549755813888 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-2405181685760 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (5360119185408 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (9380208574464 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-24120536334336 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-21161303867392 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (66443144069120 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (29424820944896 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-125292785958912 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-23031762124800 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (171356310208512 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (2163589775360 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-175683489759232 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (19019306369024 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (137644877021184 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-27195963604992 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-83252949811200 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (22123700551680 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (39005548707840 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-12441425018880 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-14122698670080 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (5101137100800 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (3920424468480 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-1548809666560 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-822805135360 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (347501281280 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (127802572800 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-56780857344 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-14240858112 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (6576507392 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (1087843328 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-517316800 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-53209728 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (25857936 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (1493856 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-737048 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-19760 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (9841 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (78 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-39 : ℤ)

def fixedRowPCoeff_43 (n : ℕ) : ℤ :=
    (if 23 = n then (274877906944 : ℤ) else 0) +
    (if 24 = n then (-549755813888 : ℤ) else 0) +
    (if 25 = n then (-2405181685760 : ℤ) else 0) +
    (if 26 = n then (5360119185408 : ℤ) else 0) +
    (if 27 = n then (9380208574464 : ℤ) else 0) +
    (if 28 = n then (-24120536334336 : ℤ) else 0) +
    (if 29 = n then (-21161303867392 : ℤ) else 0) +
    (if 30 = n then (66443144069120 : ℤ) else 0) +
    (if 31 = n then (29424820944896 : ℤ) else 0) +
    (if 32 = n then (-125292785958912 : ℤ) else 0) +
    (if 33 = n then (-23031762124800 : ℤ) else 0) +
    (if 34 = n then (171356310208512 : ℤ) else 0) +
    (if 35 = n then (2163589775360 : ℤ) else 0) +
    (if 36 = n then (-175683489759232 : ℤ) else 0) +
    (if 37 = n then (19019306369024 : ℤ) else 0) +
    (if 38 = n then (137644877021184 : ℤ) else 0) +
    (if 39 = n then (-27195963604992 : ℤ) else 0) +
    (if 40 = n then (-83252949811200 : ℤ) else 0) +
    (if 41 = n then (22123700551680 : ℤ) else 0) +
    (if 42 = n then (39005548707840 : ℤ) else 0) +
    (if 43 = n then (-12441425018880 : ℤ) else 0) +
    (if 44 = n then (-14122698670080 : ℤ) else 0) +
    (if 45 = n then (5101137100800 : ℤ) else 0) +
    (if 46 = n then (3920424468480 : ℤ) else 0) +
    (if 47 = n then (-1548809666560 : ℤ) else 0) +
    (if 48 = n then (-822805135360 : ℤ) else 0) +
    (if 49 = n then (347501281280 : ℤ) else 0) +
    (if 50 = n then (127802572800 : ℤ) else 0) +
    (if 51 = n then (-56780857344 : ℤ) else 0) +
    (if 52 = n then (-14240858112 : ℤ) else 0) +
    (if 53 = n then (6576507392 : ℤ) else 0) +
    (if 54 = n then (1087843328 : ℤ) else 0) +
    (if 55 = n then (-517316800 : ℤ) else 0) +
    (if 56 = n then (-53209728 : ℤ) else 0) +
    (if 57 = n then (25857936 : ℤ) else 0) +
    (if 58 = n then (1493856 : ℤ) else 0) +
    (if 59 = n then (-737048 : ℤ) else 0) +
    (if 60 = n then (-19760 : ℤ) else 0) +
    (if 61 = n then (9841 : ℤ) else 0) +
    (if 62 = n then (78 : ℤ) else 0) +
    (if 63 = n then (-39 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_43 (n : ℕ) :
    fixedRowPData_43.coeff n = fixedRowPCoeff_43 n := by
  simp only [fixedRowPData_43, fixedRowPCoeff_43, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_43 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_43 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_43, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_43 : ∀ k : Fin 63,
    fixedReversedTCoeff_39 (k.val + 2) - 2 * fixedReversedTCoeff_39 (k.val + 1) + fixedReversedTCoeff_39 k.val = fixedRowPCoeff_43 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_43 :
    (1 - X) ^ 2 * fixedReversedTData_39 = fixedRowPData_43 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_39, fixed_rowP_typed_coeff_43]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_39, fixed_rowP_typed_coeff_43]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_39, fixed_rowP_typed_coeff_43]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_43 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_39 _ (by omega),
              fixed_reversedT_typed_tail_39 _ (by omega), fixed_reversedT_typed_tail_39 _ hn',
              fixed_rowP_typed_tail_43 _ (by omega)]
            decide

theorem fixed_rowP_typed_43 : rowP 1 43 = fixedRowPData_43 := by
  calc
    rowP 1 43 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_39 :=
      fixedTyped_rowP_of_parameters 1 43 2 63 39 fixedChebyshevTData_39
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_39
    _ = fixedRowPData_43 := by
      rw [fixed_reversedT_typed_data_39, fixed_rowP_typed_factor_43]

def fixedRowDData_43 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 24 (274877906944 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-549755813888 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-2267742732288 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (5085241278464 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (8280696946688 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-21646635171840 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-17287243366400 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (56221121904640 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (21685289877504 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-99591701659648 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-13913546555392 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (127418794770432 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-2895881699328 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-121627031371776 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (16696567922688 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (88233895526400 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-19568001024000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-49097893478400 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (14047452856320 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (21002987765760 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-7061349335040 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-6880289095680 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (2585693061120 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (1708902973440 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-696219729920 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-316463513600 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (136931328000 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (42600857600 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-19292102656 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-4016652288 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (1882805760 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (251040768 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-120745152 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-9550464 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (4679472 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (191520 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-95000 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-1520 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (759 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_43 (n : ℕ) : ℤ :=
    (if 24 = n then (274877906944 : ℤ) else 0) +
    (if 25 = n then (-549755813888 : ℤ) else 0) +
    (if 26 = n then (-2267742732288 : ℤ) else 0) +
    (if 27 = n then (5085241278464 : ℤ) else 0) +
    (if 28 = n then (8280696946688 : ℤ) else 0) +
    (if 29 = n then (-21646635171840 : ℤ) else 0) +
    (if 30 = n then (-17287243366400 : ℤ) else 0) +
    (if 31 = n then (56221121904640 : ℤ) else 0) +
    (if 32 = n then (21685289877504 : ℤ) else 0) +
    (if 33 = n then (-99591701659648 : ℤ) else 0) +
    (if 34 = n then (-13913546555392 : ℤ) else 0) +
    (if 35 = n then (127418794770432 : ℤ) else 0) +
    (if 36 = n then (-2895881699328 : ℤ) else 0) +
    (if 37 = n then (-121627031371776 : ℤ) else 0) +
    (if 38 = n then (16696567922688 : ℤ) else 0) +
    (if 39 = n then (88233895526400 : ℤ) else 0) +
    (if 40 = n then (-19568001024000 : ℤ) else 0) +
    (if 41 = n then (-49097893478400 : ℤ) else 0) +
    (if 42 = n then (14047452856320 : ℤ) else 0) +
    (if 43 = n then (21002987765760 : ℤ) else 0) +
    (if 44 = n then (-7061349335040 : ℤ) else 0) +
    (if 45 = n then (-6880289095680 : ℤ) else 0) +
    (if 46 = n then (2585693061120 : ℤ) else 0) +
    (if 47 = n then (1708902973440 : ℤ) else 0) +
    (if 48 = n then (-696219729920 : ℤ) else 0) +
    (if 49 = n then (-316463513600 : ℤ) else 0) +
    (if 50 = n then (136931328000 : ℤ) else 0) +
    (if 51 = n then (42600857600 : ℤ) else 0) +
    (if 52 = n then (-19292102656 : ℤ) else 0) +
    (if 53 = n then (-4016652288 : ℤ) else 0) +
    (if 54 = n then (1882805760 : ℤ) else 0) +
    (if 55 = n then (251040768 : ℤ) else 0) +
    (if 56 = n then (-120745152 : ℤ) else 0) +
    (if 57 = n then (-9550464 : ℤ) else 0) +
    (if 58 = n then (4679472 : ℤ) else 0) +
    (if 59 = n then (191520 : ℤ) else 0) +
    (if 60 = n then (-95000 : ℤ) else 0) +
    (if 61 = n then (-1520 : ℤ) else 0) +
    (if 62 = n then (759 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_43 (n : ℕ) :
    fixedRowDData_43.coeff n = fixedRowDCoeff_43 n := by
  simp only [fixedRowDData_43, fixedRowDCoeff_43, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_43 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_43 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_43, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_43 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_38 (k.val + 2) - 2 * fixedReversedUCoeff_38 (k.val + 1) + fixedReversedUCoeff_38 k.val) = fixedRowDCoeff_43 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_43 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_38 = fixedRowDData_43 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_38, fixed_rowD_typed_coeff_43]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_38, fixed_rowD_typed_coeff_43]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_38, fixed_rowD_typed_coeff_43]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_43 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_38 _ (by omega),
              fixed_reversedU_typed_tail_38 _ (by omega), fixed_reversedU_typed_tail_38 _ hn',
              fixed_rowD_typed_tail_43 _ (by omega)]
            decide

theorem fixed_rowD_typed_43 : rowD 1 43 = fixedRowDData_43 := by
  calc
    rowD 1 43 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_38 :=
      fixedTyped_rowD_of_parameters 1 43 2 63 38 (1)
        fixedChebyshevUData_38 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_38
    _ = fixedRowDData_43 := by
      rw [fixed_reversedU_typed_data_38, fixed_rowD_typed_factor_43]

end InternalCatalan

end

end

end OAI
