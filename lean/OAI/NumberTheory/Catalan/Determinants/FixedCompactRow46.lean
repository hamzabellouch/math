import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT40To44
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU40To43

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_46 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 20 (2199023255552 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-4398046511104 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-20890720927744 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (46179488366592 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (89472758710272 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-225125005787136 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-225606042124288 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (676337090035712 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (362641268670464 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-1401619627376640 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-361769390309376 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (2125158407995392 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (157419141332992 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-2439996690661376 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (136938589782016 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (2166119511097344 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-330492498935808 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-1505134513225728 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (340809077489664 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (823516358246400 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-234187464376320 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-355141429493760 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (117425795235840 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (120289839022080 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-44273343528960 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-31743151964160 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (12650951147520 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (6441249669120 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-2727672053760 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-985905561600 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (437571665920 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (110762229760 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-50987901440 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-8786426880 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (4160631552 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (465163776 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-225044512 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-15074752 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (7408016 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (258720 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-128478 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-1764 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (881 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_46 (n : ℕ) : ℤ :=
    (if 20 = n then (2199023255552 : ℤ) else 0) +
    (if 21 = n then (-4398046511104 : ℤ) else 0) +
    (if 22 = n then (-20890720927744 : ℤ) else 0) +
    (if 23 = n then (46179488366592 : ℤ) else 0) +
    (if 24 = n then (89472758710272 : ℤ) else 0) +
    (if 25 = n then (-225125005787136 : ℤ) else 0) +
    (if 26 = n then (-225606042124288 : ℤ) else 0) +
    (if 27 = n then (676337090035712 : ℤ) else 0) +
    (if 28 = n then (362641268670464 : ℤ) else 0) +
    (if 29 = n then (-1401619627376640 : ℤ) else 0) +
    (if 30 = n then (-361769390309376 : ℤ) else 0) +
    (if 31 = n then (2125158407995392 : ℤ) else 0) +
    (if 32 = n then (157419141332992 : ℤ) else 0) +
    (if 33 = n then (-2439996690661376 : ℤ) else 0) +
    (if 34 = n then (136938589782016 : ℤ) else 0) +
    (if 35 = n then (2166119511097344 : ℤ) else 0) +
    (if 36 = n then (-330492498935808 : ℤ) else 0) +
    (if 37 = n then (-1505134513225728 : ℤ) else 0) +
    (if 38 = n then (340809077489664 : ℤ) else 0) +
    (if 39 = n then (823516358246400 : ℤ) else 0) +
    (if 40 = n then (-234187464376320 : ℤ) else 0) +
    (if 41 = n then (-355141429493760 : ℤ) else 0) +
    (if 42 = n then (117425795235840 : ℤ) else 0) +
    (if 43 = n then (120289839022080 : ℤ) else 0) +
    (if 44 = n then (-44273343528960 : ℤ) else 0) +
    (if 45 = n then (-31743151964160 : ℤ) else 0) +
    (if 46 = n then (12650951147520 : ℤ) else 0) +
    (if 47 = n then (6441249669120 : ℤ) else 0) +
    (if 48 = n then (-2727672053760 : ℤ) else 0) +
    (if 49 = n then (-985905561600 : ℤ) else 0) +
    (if 50 = n then (437571665920 : ℤ) else 0) +
    (if 51 = n then (110762229760 : ℤ) else 0) +
    (if 52 = n then (-50987901440 : ℤ) else 0) +
    (if 53 = n then (-8786426880 : ℤ) else 0) +
    (if 54 = n then (4160631552 : ℤ) else 0) +
    (if 55 = n then (465163776 : ℤ) else 0) +
    (if 56 = n then (-225044512 : ℤ) else 0) +
    (if 57 = n then (-15074752 : ℤ) else 0) +
    (if 58 = n then (7408016 : ℤ) else 0) +
    (if 59 = n then (258720 : ℤ) else 0) +
    (if 60 = n then (-128478 : ℤ) else 0) +
    (if 61 = n then (-1764 : ℤ) else 0) +
    (if 62 = n then (881 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_46 (n : ℕ) :
    fixedRowPData_46.coeff n = fixedRowPCoeff_46 n := by
  simp only [fixedRowPData_46, fixedRowPCoeff_46, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_46 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_46 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_46, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_46 : ∀ k : Fin 63,
    fixedReversedTCoeff_42 (k.val + 2) - 2 * fixedReversedTCoeff_42 (k.val + 1) + fixedReversedTCoeff_42 k.val = fixedRowPCoeff_46 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_46 :
    (1 - X) ^ 2 * fixedReversedTData_42 = fixedRowPData_46 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_42, fixed_rowP_typed_coeff_46]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_42, fixed_rowP_typed_coeff_46]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_42, fixed_rowP_typed_coeff_46]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_46 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_42 _ (by omega),
              fixed_reversedT_typed_tail_42 _ (by omega), fixed_reversedT_typed_tail_42 _ hn',
              fixed_rowP_typed_tail_46 _ (by omega)]
            decide

theorem fixed_rowP_typed_46 : rowP 1 46 = fixedRowPData_46 := by
  calc
    rowP 1 46 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_42 :=
      fixedTyped_rowP_of_parameters 1 46 2 63 42 fixedChebyshevTData_42
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_42
    _ = fixedRowPData_46 := by
      rw [fixed_reversedT_typed_data_42, fixed_rowP_typed_factor_46]

def fixedRowDData_46 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 21 (2199023255552 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-4398046511104 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-19791209299968 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (43980465111040 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (79852031967232 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-203684529045504 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-188016488349696 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (579717505744896 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (277463477256192 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-1134644460257280 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-242261925298176 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (1619168310853632 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (61843234095104 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-1742854779043840 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (149387552489472 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (1444079674064896 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-256164868653056 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-931749936758784 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (230584580308992 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (470580776140800 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-142277156536320 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-186026463068160 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (64372793671680 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (57280875724800 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-21838333870080 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-13604207984640 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (5575199293440 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (2453809397760 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-1062587105280 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-328635187200 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (148494417920 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (31646351360 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-14777172480 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-2092006400 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (1001701888 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (88602624 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-43224544 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-2153536 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (1064448 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (24640 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-12278 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-84 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (42 : ℤ)

def fixedRowDCoeff_46 (n : ℕ) : ℤ :=
    (if 21 = n then (2199023255552 : ℤ) else 0) +
    (if 22 = n then (-4398046511104 : ℤ) else 0) +
    (if 23 = n then (-19791209299968 : ℤ) else 0) +
    (if 24 = n then (43980465111040 : ℤ) else 0) +
    (if 25 = n then (79852031967232 : ℤ) else 0) +
    (if 26 = n then (-203684529045504 : ℤ) else 0) +
    (if 27 = n then (-188016488349696 : ℤ) else 0) +
    (if 28 = n then (579717505744896 : ℤ) else 0) +
    (if 29 = n then (277463477256192 : ℤ) else 0) +
    (if 30 = n then (-1134644460257280 : ℤ) else 0) +
    (if 31 = n then (-242261925298176 : ℤ) else 0) +
    (if 32 = n then (1619168310853632 : ℤ) else 0) +
    (if 33 = n then (61843234095104 : ℤ) else 0) +
    (if 34 = n then (-1742854779043840 : ℤ) else 0) +
    (if 35 = n then (149387552489472 : ℤ) else 0) +
    (if 36 = n then (1444079674064896 : ℤ) else 0) +
    (if 37 = n then (-256164868653056 : ℤ) else 0) +
    (if 38 = n then (-931749936758784 : ℤ) else 0) +
    (if 39 = n then (230584580308992 : ℤ) else 0) +
    (if 40 = n then (470580776140800 : ℤ) else 0) +
    (if 41 = n then (-142277156536320 : ℤ) else 0) +
    (if 42 = n then (-186026463068160 : ℤ) else 0) +
    (if 43 = n then (64372793671680 : ℤ) else 0) +
    (if 44 = n then (57280875724800 : ℤ) else 0) +
    (if 45 = n then (-21838333870080 : ℤ) else 0) +
    (if 46 = n then (-13604207984640 : ℤ) else 0) +
    (if 47 = n then (5575199293440 : ℤ) else 0) +
    (if 48 = n then (2453809397760 : ℤ) else 0) +
    (if 49 = n then (-1062587105280 : ℤ) else 0) +
    (if 50 = n then (-328635187200 : ℤ) else 0) +
    (if 51 = n then (148494417920 : ℤ) else 0) +
    (if 52 = n then (31646351360 : ℤ) else 0) +
    (if 53 = n then (-14777172480 : ℤ) else 0) +
    (if 54 = n then (-2092006400 : ℤ) else 0) +
    (if 55 = n then (1001701888 : ℤ) else 0) +
    (if 56 = n then (88602624 : ℤ) else 0) +
    (if 57 = n then (-43224544 : ℤ) else 0) +
    (if 58 = n then (-2153536 : ℤ) else 0) +
    (if 59 = n then (1064448 : ℤ) else 0) +
    (if 60 = n then (24640 : ℤ) else 0) +
    (if 61 = n then (-12278 : ℤ) else 0) +
    (if 62 = n then (-84 : ℤ) else 0) +
    (if 63 = n then (42 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_46 (n : ℕ) :
    fixedRowDData_46.coeff n = fixedRowDCoeff_46 n := by
  simp only [fixedRowDData_46, fixedRowDCoeff_46, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_46 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_46 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_46, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_46 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_41 (k.val + 2) - 2 * fixedReversedUCoeff_41 (k.val + 1) + fixedReversedUCoeff_41 k.val) = fixedRowDCoeff_46 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_46 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_41 = fixedRowDData_46 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_41, fixed_rowD_typed_coeff_46]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_41, fixed_rowD_typed_coeff_46]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_41, fixed_rowD_typed_coeff_46]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_46 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_41 _ (by omega),
              fixed_reversedU_typed_tail_41 _ (by omega), fixed_reversedU_typed_tail_41 _ hn',
              fixed_rowD_typed_tail_46 _ (by omega)]
            decide

theorem fixed_rowD_typed_46 : rowD 1 46 = fixedRowDData_46 := by
  calc
    rowD 1 46 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_41 :=
      fixedTyped_rowD_of_parameters 1 46 2 63 41 (1)
        fixedChebyshevUData_41 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_41
    _ = fixedRowDData_46 := by
      rw [fixed_reversedU_typed_data_41, fixed_rowD_typed_factor_46]

end InternalCatalan

end

end

end OAI
