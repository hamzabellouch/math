import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT32To39
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU32To39

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_42 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 24 (137438953472 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-274877906944 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-1168231104512 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (2611340115968 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (4406636445696 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-11424613007360 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-9547712299008 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (30520037605376 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (12567074308096 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-55654186221568 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-8854075080704 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (73362336382976 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-573143252992 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-72216049876992 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (9068605341696 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (54078839193600 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-11491753328640 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-31095332536320 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (8667377172480 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (13760578191360 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-4545905295360 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-4668767600640 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (1733103124480 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (1202561351680 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-485649776640 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-231261798400 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (99442573312 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (32376651776 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-14598401024 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-3179849728 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (1486234112 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (207381504 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-99566688 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-8248128 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (4037424 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (173280 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-85918 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-1444 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (721 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_42 (n : ℕ) : ℤ :=
    (if 24 = n then (137438953472 : ℤ) else 0) +
    (if 25 = n then (-274877906944 : ℤ) else 0) +
    (if 26 = n then (-1168231104512 : ℤ) else 0) +
    (if 27 = n then (2611340115968 : ℤ) else 0) +
    (if 28 = n then (4406636445696 : ℤ) else 0) +
    (if 29 = n then (-11424613007360 : ℤ) else 0) +
    (if 30 = n then (-9547712299008 : ℤ) else 0) +
    (if 31 = n then (30520037605376 : ℤ) else 0) +
    (if 32 = n then (12567074308096 : ℤ) else 0) +
    (if 33 = n then (-55654186221568 : ℤ) else 0) +
    (if 34 = n then (-8854075080704 : ℤ) else 0) +
    (if 35 = n then (73362336382976 : ℤ) else 0) +
    (if 36 = n then (-573143252992 : ℤ) else 0) +
    (if 37 = n then (-72216049876992 : ℤ) else 0) +
    (if 38 = n then (9068605341696 : ℤ) else 0) +
    (if 39 = n then (54078839193600 : ℤ) else 0) +
    (if 40 = n then (-11491753328640 : ℤ) else 0) +
    (if 41 = n then (-31095332536320 : ℤ) else 0) +
    (if 42 = n then (8667377172480 : ℤ) else 0) +
    (if 43 = n then (13760578191360 : ℤ) else 0) +
    (if 44 = n then (-4545905295360 : ℤ) else 0) +
    (if 45 = n then (-4668767600640 : ℤ) else 0) +
    (if 46 = n then (1733103124480 : ℤ) else 0) +
    (if 47 = n then (1202561351680 : ℤ) else 0) +
    (if 48 = n then (-485649776640 : ℤ) else 0) +
    (if 49 = n then (-231261798400 : ℤ) else 0) +
    (if 50 = n then (99442573312 : ℤ) else 0) +
    (if 51 = n then (32376651776 : ℤ) else 0) +
    (if 52 = n then (-14598401024 : ℤ) else 0) +
    (if 53 = n then (-3179849728 : ℤ) else 0) +
    (if 54 = n then (1486234112 : ℤ) else 0) +
    (if 55 = n then (207381504 : ℤ) else 0) +
    (if 56 = n then (-99566688 : ℤ) else 0) +
    (if 57 = n then (-8248128 : ℤ) else 0) +
    (if 58 = n then (4037424 : ℤ) else 0) +
    (if 59 = n then (173280 : ℤ) else 0) +
    (if 60 = n then (-85918 : ℤ) else 0) +
    (if 61 = n then (-1444 : ℤ) else 0) +
    (if 62 = n then (721 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_42 (n : ℕ) :
    fixedRowPData_42.coeff n = fixedRowPCoeff_42 n := by
  simp only [fixedRowPData_42, fixedRowPCoeff_42, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_42 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_42 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_42, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_42 : ∀ k : Fin 63,
    fixedReversedTCoeff_38 (k.val + 2) - 2 * fixedReversedTCoeff_38 (k.val + 1) + fixedReversedTCoeff_38 k.val = fixedRowPCoeff_42 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_42 :
    (1 - X) ^ 2 * fixedReversedTData_38 = fixedRowPData_42 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_38, fixed_rowP_typed_coeff_42]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_38, fixed_rowP_typed_coeff_42]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_38, fixed_rowP_typed_coeff_42]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_42 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_38 _ (by omega),
              fixed_reversedT_typed_tail_38 _ (by omega), fixed_reversedT_typed_tail_38 _ hn',
              fixed_rowP_typed_tail_42 _ (by omega)]
            decide

theorem fixed_rowP_typed_42 : rowP 1 42 = fixedRowPData_42 := by
  calc
    rowP 1 42 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_38 :=
      fixedTyped_rowP_of_parameters 1 42 2 63 38 fixedChebyshevTData_38
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_38
    _ = fixedRowPData_42 := by
      rw [fixed_reversedT_typed_data_38, fixed_rowP_typed_factor_42]

def fixedRowDData_42 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 25 (137438953472 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-274877906944 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-1099511627776 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (2473901162496 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (3874060500992 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-10222022164480 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-7739531067392 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (25701084299264 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (9118215569408 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-43937515438080 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-5059471474688 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (54056458387456 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-2322738446336 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-49410981494784 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (7627962580992 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (34155056332800 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-8076247695360 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-18002560942080 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (5380075683840 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (7242409574400 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-2515444039680 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-2211521495040 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (852589936640 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (506341621760 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-210569953280 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-85201715200 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (37488754688 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (10224205824 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-4693701632 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-836802560 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (396571648 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (43659264 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-21178464 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-1302336 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (642048 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (18240 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-9082 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-76 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (38 : ℤ)

def fixedRowDCoeff_42 (n : ℕ) : ℤ :=
    (if 25 = n then (137438953472 : ℤ) else 0) +
    (if 26 = n then (-274877906944 : ℤ) else 0) +
    (if 27 = n then (-1099511627776 : ℤ) else 0) +
    (if 28 = n then (2473901162496 : ℤ) else 0) +
    (if 29 = n then (3874060500992 : ℤ) else 0) +
    (if 30 = n then (-10222022164480 : ℤ) else 0) +
    (if 31 = n then (-7739531067392 : ℤ) else 0) +
    (if 32 = n then (25701084299264 : ℤ) else 0) +
    (if 33 = n then (9118215569408 : ℤ) else 0) +
    (if 34 = n then (-43937515438080 : ℤ) else 0) +
    (if 35 = n then (-5059471474688 : ℤ) else 0) +
    (if 36 = n then (54056458387456 : ℤ) else 0) +
    (if 37 = n then (-2322738446336 : ℤ) else 0) +
    (if 38 = n then (-49410981494784 : ℤ) else 0) +
    (if 39 = n then (7627962580992 : ℤ) else 0) +
    (if 40 = n then (34155056332800 : ℤ) else 0) +
    (if 41 = n then (-8076247695360 : ℤ) else 0) +
    (if 42 = n then (-18002560942080 : ℤ) else 0) +
    (if 43 = n then (5380075683840 : ℤ) else 0) +
    (if 44 = n then (7242409574400 : ℤ) else 0) +
    (if 45 = n then (-2515444039680 : ℤ) else 0) +
    (if 46 = n then (-2211521495040 : ℤ) else 0) +
    (if 47 = n then (852589936640 : ℤ) else 0) +
    (if 48 = n then (506341621760 : ℤ) else 0) +
    (if 49 = n then (-210569953280 : ℤ) else 0) +
    (if 50 = n then (-85201715200 : ℤ) else 0) +
    (if 51 = n then (37488754688 : ℤ) else 0) +
    (if 52 = n then (10224205824 : ℤ) else 0) +
    (if 53 = n then (-4693701632 : ℤ) else 0) +
    (if 54 = n then (-836802560 : ℤ) else 0) +
    (if 55 = n then (396571648 : ℤ) else 0) +
    (if 56 = n then (43659264 : ℤ) else 0) +
    (if 57 = n then (-21178464 : ℤ) else 0) +
    (if 58 = n then (-1302336 : ℤ) else 0) +
    (if 59 = n then (642048 : ℤ) else 0) +
    (if 60 = n then (18240 : ℤ) else 0) +
    (if 61 = n then (-9082 : ℤ) else 0) +
    (if 62 = n then (-76 : ℤ) else 0) +
    (if 63 = n then (38 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_42 (n : ℕ) :
    fixedRowDData_42.coeff n = fixedRowDCoeff_42 n := by
  simp only [fixedRowDData_42, fixedRowDCoeff_42, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_42 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_42 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_42, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_42 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_37 (k.val + 2) - 2 * fixedReversedUCoeff_37 (k.val + 1) + fixedReversedUCoeff_37 k.val) = fixedRowDCoeff_42 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_42 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_37 = fixedRowDData_42 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_37, fixed_rowD_typed_coeff_42]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_37, fixed_rowD_typed_coeff_42]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_37, fixed_rowD_typed_coeff_42]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_42 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_37 _ (by omega),
              fixed_reversedU_typed_tail_37 _ (by omega), fixed_reversedU_typed_tail_37 _ hn',
              fixed_rowD_typed_tail_42 _ (by omega)]
            decide

theorem fixed_rowD_typed_42 : rowD 1 42 = fixedRowDData_42 := by
  calc
    rowD 1 42 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_37 :=
      fixedTyped_rowD_of_parameters 1 42 2 63 37 (1)
        fixedChebyshevUData_37 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_37
    _ = fixedRowDData_42 := by
      rw [fixed_reversedU_typed_data_37, fixed_rowD_typed_factor_42]

end InternalCatalan

end

end

end OAI
