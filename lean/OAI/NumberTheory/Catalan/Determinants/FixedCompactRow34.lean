import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT24To31
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU24To31

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_34 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 32 (536870912 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-1073741824 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-3489660928 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (8053063680 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (9563013120 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-27179089920 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-13673431040 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (54525952000 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (8912896000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-72351744000 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (2749366272 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (66853011456 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-11374297088 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-44104417280 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (11573985280 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (20956446720 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-6906101760 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-7144243200 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (2712166400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (1719910400 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-718062592 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-283785216 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (126617088 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (30551040 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-14285440 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-1980160 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (956480 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (67200 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-33150 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-900 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (449 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_34 (n : ℕ) : ℤ :=
    (if 32 = n then (536870912 : ℤ) else 0) +
    (if 33 = n then (-1073741824 : ℤ) else 0) +
    (if 34 = n then (-3489660928 : ℤ) else 0) +
    (if 35 = n then (8053063680 : ℤ) else 0) +
    (if 36 = n then (9563013120 : ℤ) else 0) +
    (if 37 = n then (-27179089920 : ℤ) else 0) +
    (if 38 = n then (-13673431040 : ℤ) else 0) +
    (if 39 = n then (54525952000 : ℤ) else 0) +
    (if 40 = n then (8912896000 : ℤ) else 0) +
    (if 41 = n then (-72351744000 : ℤ) else 0) +
    (if 42 = n then (2749366272 : ℤ) else 0) +
    (if 43 = n then (66853011456 : ℤ) else 0) +
    (if 44 = n then (-11374297088 : ℤ) else 0) +
    (if 45 = n then (-44104417280 : ℤ) else 0) +
    (if 46 = n then (11573985280 : ℤ) else 0) +
    (if 47 = n then (20956446720 : ℤ) else 0) +
    (if 48 = n then (-6906101760 : ℤ) else 0) +
    (if 49 = n then (-7144243200 : ℤ) else 0) +
    (if 50 = n then (2712166400 : ℤ) else 0) +
    (if 51 = n then (1719910400 : ℤ) else 0) +
    (if 52 = n then (-718062592 : ℤ) else 0) +
    (if 53 = n then (-283785216 : ℤ) else 0) +
    (if 54 = n then (126617088 : ℤ) else 0) +
    (if 55 = n then (30551040 : ℤ) else 0) +
    (if 56 = n then (-14285440 : ℤ) else 0) +
    (if 57 = n then (-1980160 : ℤ) else 0) +
    (if 58 = n then (956480 : ℤ) else 0) +
    (if 59 = n then (67200 : ℤ) else 0) +
    (if 60 = n then (-33150 : ℤ) else 0) +
    (if 61 = n then (-900 : ℤ) else 0) +
    (if 62 = n then (449 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_34 (n : ℕ) :
    fixedRowPData_34.coeff n = fixedRowPCoeff_34 n := by
  simp only [fixedRowPData_34, fixedRowPCoeff_34, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_34 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_34 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_34, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_34 : ∀ k : Fin 63,
    fixedReversedTCoeff_30 (k.val + 2) - 2 * fixedReversedTCoeff_30 (k.val + 1) + fixedReversedTCoeff_30 k.val = fixedRowPCoeff_34 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_34 :
    (1 - X) ^ 2 * fixedReversedTData_30 = fixedRowPData_34 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_30, fixed_rowP_typed_coeff_34]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_30, fixed_rowP_typed_coeff_34]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_30, fixed_rowP_typed_coeff_34]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_34 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_30 _ (by omega),
              fixed_reversedT_typed_tail_30 _ (by omega), fixed_reversedT_typed_tail_30 _ hn',
              fixed_rowP_typed_tail_34 _ (by omega)]
            decide

theorem fixed_rowP_typed_34 : rowP 1 34 = fixedRowPData_34 := by
  calc
    rowP 1 34 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_30 :=
      fixedTyped_rowP_of_parameters 1 34 2 63 30 fixedChebyshevTData_30
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_30
    _ = fixedRowPData_34 := by
      rw [fixed_reversedT_typed_data_30, fixed_rowP_typed_factor_34]

def fixedRowDData_34 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 33 (536870912 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-1073741824 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-3221225472 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (7516192768 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (8019509248 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-23555211264 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-10032775168 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (43620761600 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (4718592000 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-53057945600 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (4244635648 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (44568674304 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-9053011968 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-26462650368 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (7642939392 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (11176771584 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-3921395712 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-3333980160 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (1323008000 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (687964160 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-296684544 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-94595072 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (43224064 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (8146944 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-3875456 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-396032 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (193536 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (8960 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-4450 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-60 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (30 : ℤ)

def fixedRowDCoeff_34 (n : ℕ) : ℤ :=
    (if 33 = n then (536870912 : ℤ) else 0) +
    (if 34 = n then (-1073741824 : ℤ) else 0) +
    (if 35 = n then (-3221225472 : ℤ) else 0) +
    (if 36 = n then (7516192768 : ℤ) else 0) +
    (if 37 = n then (8019509248 : ℤ) else 0) +
    (if 38 = n then (-23555211264 : ℤ) else 0) +
    (if 39 = n then (-10032775168 : ℤ) else 0) +
    (if 40 = n then (43620761600 : ℤ) else 0) +
    (if 41 = n then (4718592000 : ℤ) else 0) +
    (if 42 = n then (-53057945600 : ℤ) else 0) +
    (if 43 = n then (4244635648 : ℤ) else 0) +
    (if 44 = n then (44568674304 : ℤ) else 0) +
    (if 45 = n then (-9053011968 : ℤ) else 0) +
    (if 46 = n then (-26462650368 : ℤ) else 0) +
    (if 47 = n then (7642939392 : ℤ) else 0) +
    (if 48 = n then (11176771584 : ℤ) else 0) +
    (if 49 = n then (-3921395712 : ℤ) else 0) +
    (if 50 = n then (-3333980160 : ℤ) else 0) +
    (if 51 = n then (1323008000 : ℤ) else 0) +
    (if 52 = n then (687964160 : ℤ) else 0) +
    (if 53 = n then (-296684544 : ℤ) else 0) +
    (if 54 = n then (-94595072 : ℤ) else 0) +
    (if 55 = n then (43224064 : ℤ) else 0) +
    (if 56 = n then (8146944 : ℤ) else 0) +
    (if 57 = n then (-3875456 : ℤ) else 0) +
    (if 58 = n then (-396032 : ℤ) else 0) +
    (if 59 = n then (193536 : ℤ) else 0) +
    (if 60 = n then (8960 : ℤ) else 0) +
    (if 61 = n then (-4450 : ℤ) else 0) +
    (if 62 = n then (-60 : ℤ) else 0) +
    (if 63 = n then (30 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_34 (n : ℕ) :
    fixedRowDData_34.coeff n = fixedRowDCoeff_34 n := by
  simp only [fixedRowDData_34, fixedRowDCoeff_34, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_34 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_34 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_34, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_34 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_29 (k.val + 2) - 2 * fixedReversedUCoeff_29 (k.val + 1) + fixedReversedUCoeff_29 k.val) = fixedRowDCoeff_34 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_34 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_29 = fixedRowDData_34 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_29, fixed_rowD_typed_coeff_34]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_29, fixed_rowD_typed_coeff_34]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_29, fixed_rowD_typed_coeff_34]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_34 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_29 _ (by omega),
              fixed_reversedU_typed_tail_29 _ (by omega), fixed_reversedU_typed_tail_29 _ hn',
              fixed_rowD_typed_tail_34 _ (by omega)]
            decide

theorem fixed_rowD_typed_34 : rowD 1 34 = fixedRowDData_34 := by
  calc
    rowD 1 34 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_29 :=
      fixedTyped_rowD_of_parameters 1 34 2 63 29 (1)
        fixedChebyshevUData_29 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_29
    _ = fixedRowDData_34 := by
      rw [fixed_reversedU_typed_data_29, fixed_rowD_typed_factor_34]

end InternalCatalan

end

end

end OAI
