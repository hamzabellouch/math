import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT24To31
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU24To31

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_30 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 36 (33554432 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-67108864 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-184549376 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (436207616 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (408944640 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-1254096896 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-422576128 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (2099249152 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (83492864 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-2266234880 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (307560448 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (1651113984 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-412778496 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-825556992 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (271564800 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (282427392 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-108852224 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-64722944 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (27602432 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (9518080 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-4342624 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-832832 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (397488 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (37856 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-18590 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-676 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (337 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_30 (n : ℕ) : ℤ :=
    (if 36 = n then (33554432 : ℤ) else 0) +
    (if 37 = n then (-67108864 : ℤ) else 0) +
    (if 38 = n then (-184549376 : ℤ) else 0) +
    (if 39 = n then (436207616 : ℤ) else 0) +
    (if 40 = n then (408944640 : ℤ) else 0) +
    (if 41 = n then (-1254096896 : ℤ) else 0) +
    (if 42 = n then (-422576128 : ℤ) else 0) +
    (if 43 = n then (2099249152 : ℤ) else 0) +
    (if 44 = n then (83492864 : ℤ) else 0) +
    (if 45 = n then (-2266234880 : ℤ) else 0) +
    (if 46 = n then (307560448 : ℤ) else 0) +
    (if 47 = n then (1651113984 : ℤ) else 0) +
    (if 48 = n then (-412778496 : ℤ) else 0) +
    (if 49 = n then (-825556992 : ℤ) else 0) +
    (if 50 = n then (271564800 : ℤ) else 0) +
    (if 51 = n then (282427392 : ℤ) else 0) +
    (if 52 = n then (-108852224 : ℤ) else 0) +
    (if 53 = n then (-64722944 : ℤ) else 0) +
    (if 54 = n then (27602432 : ℤ) else 0) +
    (if 55 = n then (9518080 : ℤ) else 0) +
    (if 56 = n then (-4342624 : ℤ) else 0) +
    (if 57 = n then (-832832 : ℤ) else 0) +
    (if 58 = n then (397488 : ℤ) else 0) +
    (if 59 = n then (37856 : ℤ) else 0) +
    (if 60 = n then (-18590 : ℤ) else 0) +
    (if 61 = n then (-676 : ℤ) else 0) +
    (if 62 = n then (337 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_30 (n : ℕ) :
    fixedRowPData_30.coeff n = fixedRowPCoeff_30 n := by
  simp only [fixedRowPData_30, fixedRowPCoeff_30, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_30 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_30 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_30, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_30 : ∀ k : Fin 63,
    fixedReversedTCoeff_26 (k.val + 2) - 2 * fixedReversedTCoeff_26 (k.val + 1) + fixedReversedTCoeff_26 k.val = fixedRowPCoeff_30 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_30 :
    (1 - X) ^ 2 * fixedReversedTData_26 = fixedRowPData_30 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_26, fixed_rowP_typed_coeff_30]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_26, fixed_rowP_typed_coeff_30]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_26, fixed_rowP_typed_coeff_30]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_30 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_26 _ (by omega),
              fixed_reversedT_typed_tail_26 _ (by omega), fixed_reversedT_typed_tail_26 _ hn',
              fixed_rowP_typed_tail_30 _ (by omega)]
            decide

theorem fixed_rowP_typed_30 : rowP 1 30 = fixedRowPData_30 := by
  calc
    rowP 1 30 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_26 :=
      fixedTyped_rowP_of_parameters 1 30 2 63 26 fixedChebyshevTData_26
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_26
    _ = fixedRowPData_30 := by
      rw [fixed_reversedT_typed_data_26, fixed_rowP_typed_factor_30]

def fixedRowDData_30 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 37 (33554432 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-67108864 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-167772160 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (402653184 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (329252864 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-1061158912 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-276824064 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (1614807040 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-22937600 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-1568931840 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (276430848 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (1016070144 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-285769728 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-444530688 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (157089792 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (130351104 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-52728832 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-24893440 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (10982400 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (2928640 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-1368224 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-192192 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (93184 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (5824 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-2886 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-52 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (26 : ℤ)

def fixedRowDCoeff_30 (n : ℕ) : ℤ :=
    (if 37 = n then (33554432 : ℤ) else 0) +
    (if 38 = n then (-67108864 : ℤ) else 0) +
    (if 39 = n then (-167772160 : ℤ) else 0) +
    (if 40 = n then (402653184 : ℤ) else 0) +
    (if 41 = n then (329252864 : ℤ) else 0) +
    (if 42 = n then (-1061158912 : ℤ) else 0) +
    (if 43 = n then (-276824064 : ℤ) else 0) +
    (if 44 = n then (1614807040 : ℤ) else 0) +
    (if 45 = n then (-22937600 : ℤ) else 0) +
    (if 46 = n then (-1568931840 : ℤ) else 0) +
    (if 47 = n then (276430848 : ℤ) else 0) +
    (if 48 = n then (1016070144 : ℤ) else 0) +
    (if 49 = n then (-285769728 : ℤ) else 0) +
    (if 50 = n then (-444530688 : ℤ) else 0) +
    (if 51 = n then (157089792 : ℤ) else 0) +
    (if 52 = n then (130351104 : ℤ) else 0) +
    (if 53 = n then (-52728832 : ℤ) else 0) +
    (if 54 = n then (-24893440 : ℤ) else 0) +
    (if 55 = n then (10982400 : ℤ) else 0) +
    (if 56 = n then (2928640 : ℤ) else 0) +
    (if 57 = n then (-1368224 : ℤ) else 0) +
    (if 58 = n then (-192192 : ℤ) else 0) +
    (if 59 = n then (93184 : ℤ) else 0) +
    (if 60 = n then (5824 : ℤ) else 0) +
    (if 61 = n then (-2886 : ℤ) else 0) +
    (if 62 = n then (-52 : ℤ) else 0) +
    (if 63 = n then (26 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_30 (n : ℕ) :
    fixedRowDData_30.coeff n = fixedRowDCoeff_30 n := by
  simp only [fixedRowDData_30, fixedRowDCoeff_30, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_30 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_30 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_30, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_30 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_25 (k.val + 2) - 2 * fixedReversedUCoeff_25 (k.val + 1) + fixedReversedUCoeff_25 k.val) = fixedRowDCoeff_30 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_30 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_25 = fixedRowDData_30 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_25, fixed_rowD_typed_coeff_30]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_25, fixed_rowD_typed_coeff_30]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_25, fixed_rowD_typed_coeff_30]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_30 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_25 _ (by omega),
              fixed_reversedU_typed_tail_25 _ (by omega), fixed_reversedU_typed_tail_25 _ hn',
              fixed_rowD_typed_tail_30 _ (by omega)]
            decide

theorem fixed_rowD_typed_30 : rowD 1 30 = fixedRowDData_30 := by
  calc
    rowD 1 30 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_25 :=
      fixedTyped_rowD_of_parameters 1 30 2 63 25 (1)
        fixedChebyshevUData_25 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_25
    _ = fixedRowDData_30 := by
      rw [fixed_reversedU_typed_data_25, fixed_rowD_typed_factor_30]

end InternalCatalan

end

end

end OAI
