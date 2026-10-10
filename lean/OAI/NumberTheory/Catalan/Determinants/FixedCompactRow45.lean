import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT40To44
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU40To43

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_45 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 21 (1099511627776 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-2199023255552 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-10170482556928 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (22539988369408 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (42262478192640 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-107064944754688 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-102838696935424 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (312742338625536 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (157956012244992 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-628654363115520 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-146686018060288 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (922026399236096 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (49394271387648 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-1020814942011392 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (75059922206720 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (870695097597952 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-145940371472384 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-578814354653184 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (138674272468992 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (301465809715200 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-89224154972160 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-123017499770880 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (41937784012800 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (39141931745280 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-14762582016000 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-9616767713280 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (3910114344960 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (1796539023360 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-773509857280 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-249519308800 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (112283688960 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (24951930880 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-11618242816 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-1715445248 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (819881920 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (75681408 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-36880976 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-1919456 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (948248 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (22960 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-11439 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-82 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (41 : ℤ)

def fixedRowPCoeff_45 (n : ℕ) : ℤ :=
    (if 21 = n then (1099511627776 : ℤ) else 0) +
    (if 22 = n then (-2199023255552 : ℤ) else 0) +
    (if 23 = n then (-10170482556928 : ℤ) else 0) +
    (if 24 = n then (22539988369408 : ℤ) else 0) +
    (if 25 = n then (42262478192640 : ℤ) else 0) +
    (if 26 = n then (-107064944754688 : ℤ) else 0) +
    (if 27 = n then (-102838696935424 : ℤ) else 0) +
    (if 28 = n then (312742338625536 : ℤ) else 0) +
    (if 29 = n then (157956012244992 : ℤ) else 0) +
    (if 30 = n then (-628654363115520 : ℤ) else 0) +
    (if 31 = n then (-146686018060288 : ℤ) else 0) +
    (if 32 = n then (922026399236096 : ℤ) else 0) +
    (if 33 = n then (49394271387648 : ℤ) else 0) +
    (if 34 = n then (-1020814942011392 : ℤ) else 0) +
    (if 35 = n then (75059922206720 : ℤ) else 0) +
    (if 36 = n then (870695097597952 : ℤ) else 0) +
    (if 37 = n then (-145940371472384 : ℤ) else 0) +
    (if 38 = n then (-578814354653184 : ℤ) else 0) +
    (if 39 = n then (138674272468992 : ℤ) else 0) +
    (if 40 = n then (301465809715200 : ℤ) else 0) +
    (if 41 = n then (-89224154972160 : ℤ) else 0) +
    (if 42 = n then (-123017499770880 : ℤ) else 0) +
    (if 43 = n then (41937784012800 : ℤ) else 0) +
    (if 44 = n then (39141931745280 : ℤ) else 0) +
    (if 45 = n then (-14762582016000 : ℤ) else 0) +
    (if 46 = n then (-9616767713280 : ℤ) else 0) +
    (if 47 = n then (3910114344960 : ℤ) else 0) +
    (if 48 = n then (1796539023360 : ℤ) else 0) +
    (if 49 = n then (-773509857280 : ℤ) else 0) +
    (if 50 = n then (-249519308800 : ℤ) else 0) +
    (if 51 = n then (112283688960 : ℤ) else 0) +
    (if 52 = n then (24951930880 : ℤ) else 0) +
    (if 53 = n then (-11618242816 : ℤ) else 0) +
    (if 54 = n then (-1715445248 : ℤ) else 0) +
    (if 55 = n then (819881920 : ℤ) else 0) +
    (if 56 = n then (75681408 : ℤ) else 0) +
    (if 57 = n then (-36880976 : ℤ) else 0) +
    (if 58 = n then (-1919456 : ℤ) else 0) +
    (if 59 = n then (948248 : ℤ) else 0) +
    (if 60 = n then (22960 : ℤ) else 0) +
    (if 61 = n then (-11439 : ℤ) else 0) +
    (if 62 = n then (-82 : ℤ) else 0) +
    (if 63 = n then (41 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_45 (n : ℕ) :
    fixedRowPData_45.coeff n = fixedRowPCoeff_45 n := by
  simp only [fixedRowPData_45, fixedRowPCoeff_45, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_45 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_45 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_45, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_45 : ∀ k : Fin 63,
    fixedReversedTCoeff_41 (k.val + 2) - 2 * fixedReversedTCoeff_41 (k.val + 1) + fixedReversedTCoeff_41 k.val = fixedRowPCoeff_45 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_45 :
    (1 - X) ^ 2 * fixedReversedTData_41 = fixedRowPData_45 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_41, fixed_rowP_typed_coeff_45]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_41, fixed_rowP_typed_coeff_45]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_41, fixed_rowP_typed_coeff_45]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_45 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_41 _ (by omega),
              fixed_reversedT_typed_tail_41 _ (by omega), fixed_reversedT_typed_tail_41 _ hn',
              fixed_rowP_typed_tail_45 _ (by omega)]
            decide

theorem fixed_rowP_typed_45 : rowP 1 45 = fixedRowPData_45 := by
  calc
    rowP 1 45 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_41 :=
      fixedTyped_rowP_of_parameters 1 45 2 63 41 fixedChebyshevTData_41
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_41
    _ = fixedRowPData_45 := by
      rw [fixed_reversedT_typed_data_41, fixed_rowP_typed_factor_45]

def fixedRowDData_45 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 22 (1099511627776 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-2199023255552 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-9620726743040 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (21440476741632 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (37589553774592 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-96619584290816 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-85177791414272 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (266975167119360 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (119507465011200 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-505990097141760 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-95575907237888 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (697141911617536 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (12448962707456 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-722039837032448 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (74327630282752 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (573384576466944 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-110224497180672 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-352935582105600 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (91910307840000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (169114966425600 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-53053001564160 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-63008963297280 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (22435009658880 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (18138943979520 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-7075751854080 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-3987440271360 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (1665084948480 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (657270374400 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-289077248000 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-79115878400 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (36210728960 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (6694420480 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-3158929664 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-376561152 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (181819968 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (12921216 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-6343568 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-234080 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (116200 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1680 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-839 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_45 (n : ℕ) : ℤ :=
    (if 22 = n then (1099511627776 : ℤ) else 0) +
    (if 23 = n then (-2199023255552 : ℤ) else 0) +
    (if 24 = n then (-9620726743040 : ℤ) else 0) +
    (if 25 = n then (21440476741632 : ℤ) else 0) +
    (if 26 = n then (37589553774592 : ℤ) else 0) +
    (if 27 = n then (-96619584290816 : ℤ) else 0) +
    (if 28 = n then (-85177791414272 : ℤ) else 0) +
    (if 29 = n then (266975167119360 : ℤ) else 0) +
    (if 30 = n then (119507465011200 : ℤ) else 0) +
    (if 31 = n then (-505990097141760 : ℤ) else 0) +
    (if 32 = n then (-95575907237888 : ℤ) else 0) +
    (if 33 = n then (697141911617536 : ℤ) else 0) +
    (if 34 = n then (12448962707456 : ℤ) else 0) +
    (if 35 = n then (-722039837032448 : ℤ) else 0) +
    (if 36 = n then (74327630282752 : ℤ) else 0) +
    (if 37 = n then (573384576466944 : ℤ) else 0) +
    (if 38 = n then (-110224497180672 : ℤ) else 0) +
    (if 39 = n then (-352935582105600 : ℤ) else 0) +
    (if 40 = n then (91910307840000 : ℤ) else 0) +
    (if 41 = n then (169114966425600 : ℤ) else 0) +
    (if 42 = n then (-53053001564160 : ℤ) else 0) +
    (if 43 = n then (-63008963297280 : ℤ) else 0) +
    (if 44 = n then (22435009658880 : ℤ) else 0) +
    (if 45 = n then (18138943979520 : ℤ) else 0) +
    (if 46 = n then (-7075751854080 : ℤ) else 0) +
    (if 47 = n then (-3987440271360 : ℤ) else 0) +
    (if 48 = n then (1665084948480 : ℤ) else 0) +
    (if 49 = n then (657270374400 : ℤ) else 0) +
    (if 50 = n then (-289077248000 : ℤ) else 0) +
    (if 51 = n then (-79115878400 : ℤ) else 0) +
    (if 52 = n then (36210728960 : ℤ) else 0) +
    (if 53 = n then (6694420480 : ℤ) else 0) +
    (if 54 = n then (-3158929664 : ℤ) else 0) +
    (if 55 = n then (-376561152 : ℤ) else 0) +
    (if 56 = n then (181819968 : ℤ) else 0) +
    (if 57 = n then (12921216 : ℤ) else 0) +
    (if 58 = n then (-6343568 : ℤ) else 0) +
    (if 59 = n then (-234080 : ℤ) else 0) +
    (if 60 = n then (116200 : ℤ) else 0) +
    (if 61 = n then (1680 : ℤ) else 0) +
    (if 62 = n then (-839 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_45 (n : ℕ) :
    fixedRowDData_45.coeff n = fixedRowDCoeff_45 n := by
  simp only [fixedRowDData_45, fixedRowDCoeff_45, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_45 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_45 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_45, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_45 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_40 (k.val + 2) - 2 * fixedReversedUCoeff_40 (k.val + 1) + fixedReversedUCoeff_40 k.val) = fixedRowDCoeff_45 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_45 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_40 = fixedRowDData_45 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_40, fixed_rowD_typed_coeff_45]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_40, fixed_rowD_typed_coeff_45]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_40, fixed_rowD_typed_coeff_45]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_45 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_40 _ (by omega),
              fixed_reversedU_typed_tail_40 _ (by omega), fixed_reversedU_typed_tail_40 _ hn',
              fixed_rowD_typed_tail_45 _ (by omega)]
            decide

theorem fixed_rowD_typed_45 : rowD 1 45 = fixedRowDData_45 := by
  calc
    rowD 1 45 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_40 :=
      fixedTyped_rowD_of_parameters 1 45 2 63 40 (1)
        fixedChebyshevUData_40 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_40
    _ = fixedRowDData_45 := by
      rw [fixed_reversedU_typed_data_40, fixed_rowD_typed_factor_45]

end InternalCatalan

end

end

end OAI
