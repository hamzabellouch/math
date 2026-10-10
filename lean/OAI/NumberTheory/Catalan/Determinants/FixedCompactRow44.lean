import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT40To44
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU32To39

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_44 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 22 (549755813888 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-1099511627776 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-4947802324992 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (10995116277760 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (19928648253440 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-50852412784640 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-46729244180480 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (144310901145600 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (68397354188800 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-281105609523200 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-58630598557696 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (398366806638592 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (13181254631424 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-424729315901440 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (38611755991040 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (347505803919360 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-63460532551680 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-220584738816000 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (55739154432000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (109106429952000 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-33550227210240 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-42005975531520 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (14748179496960 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (12509616537600 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-4830722457600 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-2848171622400 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (1180652339200 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (486866944000 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-213004288000 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-60858368000 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (27751415808 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (5355536384 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-2520867712 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-313800960 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (151282560 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (11235840 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-5511520 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-212800 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (105600 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1600 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-799 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_44 (n : ℕ) : ℤ :=
    (if 22 = n then (549755813888 : ℤ) else 0) +
    (if 23 = n then (-1099511627776 : ℤ) else 0) +
    (if 24 = n then (-4947802324992 : ℤ) else 0) +
    (if 25 = n then (10995116277760 : ℤ) else 0) +
    (if 26 = n then (19928648253440 : ℤ) else 0) +
    (if 27 = n then (-50852412784640 : ℤ) else 0) +
    (if 28 = n then (-46729244180480 : ℤ) else 0) +
    (if 29 = n then (144310901145600 : ℤ) else 0) +
    (if 30 = n then (68397354188800 : ℤ) else 0) +
    (if 31 = n then (-281105609523200 : ℤ) else 0) +
    (if 32 = n then (-58630598557696 : ℤ) else 0) +
    (if 33 = n then (398366806638592 : ℤ) else 0) +
    (if 34 = n then (13181254631424 : ℤ) else 0) +
    (if 35 = n then (-424729315901440 : ℤ) else 0) +
    (if 36 = n then (38611755991040 : ℤ) else 0) +
    (if 37 = n then (347505803919360 : ℤ) else 0) +
    (if 38 = n then (-63460532551680 : ℤ) else 0) +
    (if 39 = n then (-220584738816000 : ℤ) else 0) +
    (if 40 = n then (55739154432000 : ℤ) else 0) +
    (if 41 = n then (109106429952000 : ℤ) else 0) +
    (if 42 = n then (-33550227210240 : ℤ) else 0) +
    (if 43 = n then (-42005975531520 : ℤ) else 0) +
    (if 44 = n then (14748179496960 : ℤ) else 0) +
    (if 45 = n then (12509616537600 : ℤ) else 0) +
    (if 46 = n then (-4830722457600 : ℤ) else 0) +
    (if 47 = n then (-2848171622400 : ℤ) else 0) +
    (if 48 = n then (1180652339200 : ℤ) else 0) +
    (if 49 = n then (486866944000 : ℤ) else 0) +
    (if 50 = n then (-213004288000 : ℤ) else 0) +
    (if 51 = n then (-60858368000 : ℤ) else 0) +
    (if 52 = n then (27751415808 : ℤ) else 0) +
    (if 53 = n then (5355536384 : ℤ) else 0) +
    (if 54 = n then (-2520867712 : ℤ) else 0) +
    (if 55 = n then (-313800960 : ℤ) else 0) +
    (if 56 = n then (151282560 : ℤ) else 0) +
    (if 57 = n then (11235840 : ℤ) else 0) +
    (if 58 = n then (-5511520 : ℤ) else 0) +
    (if 59 = n then (-212800 : ℤ) else 0) +
    (if 60 = n then (105600 : ℤ) else 0) +
    (if 61 = n then (1600 : ℤ) else 0) +
    (if 62 = n then (-799 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_44 (n : ℕ) :
    fixedRowPData_44.coeff n = fixedRowPCoeff_44 n := by
  simp only [fixedRowPData_44, fixedRowPCoeff_44, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_44 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_44 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_44, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_44 : ∀ k : Fin 63,
    fixedReversedTCoeff_40 (k.val + 2) - 2 * fixedReversedTCoeff_40 (k.val + 1) + fixedReversedTCoeff_40 k.val = fixedRowPCoeff_44 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_44 :
    (1 - X) ^ 2 * fixedReversedTData_40 = fixedRowPData_44 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_40, fixed_rowP_typed_coeff_44]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_40, fixed_rowP_typed_coeff_44]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_40, fixed_rowP_typed_coeff_44]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_44 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_40 _ (by omega),
              fixed_reversedT_typed_tail_40 _ (by omega), fixed_reversedT_typed_tail_40 _ hn',
              fixed_rowP_typed_tail_44 _ (by omega)]
            decide

theorem fixed_rowP_typed_44 : rowP 1 44 = fixedRowPData_44 := by
  calc
    rowP 1 44 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_40 :=
      fixedTyped_rowP_of_parameters 1 44 2 63 40 fixedChebyshevTData_40
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_40
    _ = fixedRowPData_44 := by
      rw [fixed_reversedT_typed_data_40, fixed_rowP_typed_factor_44]

def fixedRowDData_44 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 23 (549755813888 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-1099511627776 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-4672924418048 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (10445360463872 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (17660905521152 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-45767171506176 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-38448547233792 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (122664265973760 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (51110110822400 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-224884487618560 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-36945308680192 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (298775104978944 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-732291923968 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-297310521131008 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (35715874291712 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (225878772547584 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-46763964628992 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-132350843289600 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (36171153408000 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (60008536473600 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-19502774353920 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-21002987765760 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (7686830161920 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (5629327441920 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-2245029396480 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-1139268648960 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (484432609280 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (170403430400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-76072960000 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-18257510400 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (8459313152 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (1338884096 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-638061952 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-62760192 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (30537408 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (1685376 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-832048 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-21280 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (10600 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (80 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-40 : ℤ)

def fixedRowDCoeff_44 (n : ℕ) : ℤ :=
    (if 23 = n then (549755813888 : ℤ) else 0) +
    (if 24 = n then (-1099511627776 : ℤ) else 0) +
    (if 25 = n then (-4672924418048 : ℤ) else 0) +
    (if 26 = n then (10445360463872 : ℤ) else 0) +
    (if 27 = n then (17660905521152 : ℤ) else 0) +
    (if 28 = n then (-45767171506176 : ℤ) else 0) +
    (if 29 = n then (-38448547233792 : ℤ) else 0) +
    (if 30 = n then (122664265973760 : ℤ) else 0) +
    (if 31 = n then (51110110822400 : ℤ) else 0) +
    (if 32 = n then (-224884487618560 : ℤ) else 0) +
    (if 33 = n then (-36945308680192 : ℤ) else 0) +
    (if 34 = n then (298775104978944 : ℤ) else 0) +
    (if 35 = n then (-732291923968 : ℤ) else 0) +
    (if 36 = n then (-297310521131008 : ℤ) else 0) +
    (if 37 = n then (35715874291712 : ℤ) else 0) +
    (if 38 = n then (225878772547584 : ℤ) else 0) +
    (if 39 = n then (-46763964628992 : ℤ) else 0) +
    (if 40 = n then (-132350843289600 : ℤ) else 0) +
    (if 41 = n then (36171153408000 : ℤ) else 0) +
    (if 42 = n then (60008536473600 : ℤ) else 0) +
    (if 43 = n then (-19502774353920 : ℤ) else 0) +
    (if 44 = n then (-21002987765760 : ℤ) else 0) +
    (if 45 = n then (7686830161920 : ℤ) else 0) +
    (if 46 = n then (5629327441920 : ℤ) else 0) +
    (if 47 = n then (-2245029396480 : ℤ) else 0) +
    (if 48 = n then (-1139268648960 : ℤ) else 0) +
    (if 49 = n then (484432609280 : ℤ) else 0) +
    (if 50 = n then (170403430400 : ℤ) else 0) +
    (if 51 = n then (-76072960000 : ℤ) else 0) +
    (if 52 = n then (-18257510400 : ℤ) else 0) +
    (if 53 = n then (8459313152 : ℤ) else 0) +
    (if 54 = n then (1338884096 : ℤ) else 0) +
    (if 55 = n then (-638061952 : ℤ) else 0) +
    (if 56 = n then (-62760192 : ℤ) else 0) +
    (if 57 = n then (30537408 : ℤ) else 0) +
    (if 58 = n then (1685376 : ℤ) else 0) +
    (if 59 = n then (-832048 : ℤ) else 0) +
    (if 60 = n then (-21280 : ℤ) else 0) +
    (if 61 = n then (10600 : ℤ) else 0) +
    (if 62 = n then (80 : ℤ) else 0) +
    (if 63 = n then (-40 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_44 (n : ℕ) :
    fixedRowDData_44.coeff n = fixedRowDCoeff_44 n := by
  simp only [fixedRowDData_44, fixedRowDCoeff_44, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_44 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_44 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_44, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_44 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_39 (k.val + 2) - 2 * fixedReversedUCoeff_39 (k.val + 1) + fixedReversedUCoeff_39 k.val) = fixedRowDCoeff_44 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_44 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_39 = fixedRowDData_44 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_39, fixed_rowD_typed_coeff_44]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_39, fixed_rowD_typed_coeff_44]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_39, fixed_rowD_typed_coeff_44]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_44 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_39 _ (by omega),
              fixed_reversedU_typed_tail_39 _ (by omega), fixed_reversedU_typed_tail_39 _ hn',
              fixed_rowD_typed_tail_44 _ (by omega)]
            decide

theorem fixed_rowD_typed_44 : rowD 1 44 = fixedRowDData_44 := by
  calc
    rowD 1 44 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_39 :=
      fixedTyped_rowD_of_parameters 1 44 2 63 39 (1)
        fixedChebyshevUData_39 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_39
    _ = fixedRowDData_44 := by
      rw [fixed_reversedU_typed_data_39, fixed_rowD_typed_factor_44]

end InternalCatalan

end

end

end OAI
