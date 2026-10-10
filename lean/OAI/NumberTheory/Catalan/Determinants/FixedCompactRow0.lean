import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_0 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 58 (8 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-16 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (16 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-7 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_0 (n : ℕ) : ℤ :=
    (if 58 = n then (8 : ℤ) else 0) +
    (if 59 = n then (-16 : ℤ) else 0) +
    (if 61 = n then (16 : ℤ) else 0) +
    (if 62 = n then (-7 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_0 (n : ℕ) :
    fixedRowPData_0.coeff n = fixedRowPCoeff_0 n := by
  simp only [fixedRowPData_0, fixedRowPCoeff_0, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_0 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_0 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_0, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_0 : ∀ k : Fin 63,
    fixedReversedTCoeff_4 (k.val + 2) - 2 * fixedReversedTCoeff_4 (k.val + 1) + fixedReversedTCoeff_4 k.val = fixedRowPCoeff_0 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_0 :
    (1 - X) ^ 2 * fixedReversedTData_4 = fixedRowPData_0 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_4, fixed_rowP_typed_coeff_0]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_4, fixed_rowP_typed_coeff_0]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_4, fixed_rowP_typed_coeff_0]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_0 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_4 _ (by omega),
              fixed_reversedT_typed_tail_4 _ (by omega), fixed_reversedT_typed_tail_4 _ hn',
              fixed_rowP_typed_tail_0 _ (by omega)]
            decide

theorem fixed_rowP_typed_0 : rowP 1 0 = fixedRowPData_0 := by
  calc
    rowP 1 0 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_4 :=
      fixedTyped_rowP_of_parameters 1 0 2 63 4 fixedChebyshevTData_4
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_4
    _ = fixedRowPData_0 := by
      rw [fixed_reversedT_typed_data_4, fixed_rowP_typed_factor_0]

def fixedRowDData_0 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 59 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (16 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-4 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (4 : ℤ)

def fixedRowDCoeff_0 (n : ℕ) : ℤ :=
    (if 59 = n then (-8 : ℤ) else 0) +
    (if 60 = n then (16 : ℤ) else 0) +
    (if 61 = n then (-4 : ℤ) else 0) +
    (if 62 = n then (-8 : ℤ) else 0) +
    (if 63 = n then (4 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_0 (n : ℕ) :
    fixedRowDData_0.coeff n = fixedRowDCoeff_0 n := by
  simp only [fixedRowDData_0, fixedRowDCoeff_0, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_0 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_0 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_0, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_0 : ∀ k : Fin 63,
    (-1 : ℤ) * (fixedReversedUCoeff_3 (k.val + 2) - 2 * fixedReversedUCoeff_3 (k.val + 1) + fixedReversedUCoeff_3 k.val) = fixedRowDCoeff_0 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_0 :
    Polynomial.C (-1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_3 = fixedRowDData_0 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_3, fixed_rowD_typed_coeff_0]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_3, fixed_rowD_typed_coeff_0]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_3, fixed_rowD_typed_coeff_0]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_0 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_3 _ (by omega),
              fixed_reversedU_typed_tail_3 _ (by omega), fixed_reversedU_typed_tail_3 _ hn',
              fixed_rowD_typed_tail_0 _ (by omega)]
            decide

theorem fixed_rowD_typed_0 : rowD 1 0 = fixedRowDData_0 := by
  calc
    rowD 1 0 = Polynomial.C (-1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_3 :=
      fixedTyped_rowD_of_parameters 1 0 2 63 3 (-1)
        fixedChebyshevUData_3 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_3
    _ = fixedRowDData_0 := by
      rw [fixed_reversedU_typed_data_3, fixed_rowD_typed_factor_0]

end InternalCatalan

end

end

end OAI
