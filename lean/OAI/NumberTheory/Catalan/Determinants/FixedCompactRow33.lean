import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT24To31
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU24To31

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_33 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 33 (268435456 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-536870912 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-1677721600 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (3892314112 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (4378853376 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-12650020864 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-5838471168 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (24326963200 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (3223322624 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-30773608448 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (1923350528 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (26926907392 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-5121966080 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-16682975232 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (4658233344 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (7366508544 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-2532237312 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-2302033920 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (901629952 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (498774016 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-213291520 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-72190976 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (32814080 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (6562816 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-3112512 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-337792 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (164836 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (8120 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-4031 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-58 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (29 : ℤ)

def fixedRowPCoeff_33 (n : ℕ) : ℤ :=
    (if 33 = n then (268435456 : ℤ) else 0) +
    (if 34 = n then (-536870912 : ℤ) else 0) +
    (if 35 = n then (-1677721600 : ℤ) else 0) +
    (if 36 = n then (3892314112 : ℤ) else 0) +
    (if 37 = n then (4378853376 : ℤ) else 0) +
    (if 38 = n then (-12650020864 : ℤ) else 0) +
    (if 39 = n then (-5838471168 : ℤ) else 0) +
    (if 40 = n then (24326963200 : ℤ) else 0) +
    (if 41 = n then (3223322624 : ℤ) else 0) +
    (if 42 = n then (-30773608448 : ℤ) else 0) +
    (if 43 = n then (1923350528 : ℤ) else 0) +
    (if 44 = n then (26926907392 : ℤ) else 0) +
    (if 45 = n then (-5121966080 : ℤ) else 0) +
    (if 46 = n then (-16682975232 : ℤ) else 0) +
    (if 47 = n then (4658233344 : ℤ) else 0) +
    (if 48 = n then (7366508544 : ℤ) else 0) +
    (if 49 = n then (-2532237312 : ℤ) else 0) +
    (if 50 = n then (-2302033920 : ℤ) else 0) +
    (if 51 = n then (901629952 : ℤ) else 0) +
    (if 52 = n then (498774016 : ℤ) else 0) +
    (if 53 = n then (-213291520 : ℤ) else 0) +
    (if 54 = n then (-72190976 : ℤ) else 0) +
    (if 55 = n then (32814080 : ℤ) else 0) +
    (if 56 = n then (6562816 : ℤ) else 0) +
    (if 57 = n then (-3112512 : ℤ) else 0) +
    (if 58 = n then (-337792 : ℤ) else 0) +
    (if 59 = n then (164836 : ℤ) else 0) +
    (if 60 = n then (8120 : ℤ) else 0) +
    (if 61 = n then (-4031 : ℤ) else 0) +
    (if 62 = n then (-58 : ℤ) else 0) +
    (if 63 = n then (29 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_33 (n : ℕ) :
    fixedRowPData_33.coeff n = fixedRowPCoeff_33 n := by
  simp only [fixedRowPData_33, fixedRowPCoeff_33, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_33 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_33 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_33, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_33 : ∀ k : Fin 63,
    fixedReversedTCoeff_29 (k.val + 2) - 2 * fixedReversedTCoeff_29 (k.val + 1) + fixedReversedTCoeff_29 k.val = fixedRowPCoeff_33 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_33 :
    (1 - X) ^ 2 * fixedReversedTData_29 = fixedRowPData_33 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_29, fixed_rowP_typed_coeff_33]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_29, fixed_rowP_typed_coeff_33]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_29, fixed_rowP_typed_coeff_33]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_33 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_29 _ (by omega),
              fixed_reversedT_typed_tail_29 _ (by omega), fixed_reversedT_typed_tail_29 _ hn',
              fixed_rowP_typed_tail_33 _ (by omega)]
            decide

theorem fixed_rowP_typed_33 : rowP 1 33 = fixedRowPData_33 := by
  calc
    rowP 1 33 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_29 :=
      fixedTyped_rowP_of_parameters 1 33 2 63 29 fixedChebyshevTData_29
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_29
    _ = fixedRowPData_33 := by
      rw [fixed_reversedT_typed_data_29, fixed_rowP_typed_factor_33]

def fixedRowDData_33 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 34 (268435456 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-536870912 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-1543503872 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (3623878656 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (3640655872 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-10905190400 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-4194304000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (19293798400 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (1495269376 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-22284337152 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (2321285120 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (17641766912 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-3931045888 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-9779675136 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (2984706048 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (3810263040 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-1389158400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-1031946240 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (421378048 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (189190144 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-83393024 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-22404096 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (10409984 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (1584128 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-762944 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-58240 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (28700 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (840 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-419 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_33 (n : ℕ) : ℤ :=
    (if 34 = n then (268435456 : ℤ) else 0) +
    (if 35 = n then (-536870912 : ℤ) else 0) +
    (if 36 = n then (-1543503872 : ℤ) else 0) +
    (if 37 = n then (3623878656 : ℤ) else 0) +
    (if 38 = n then (3640655872 : ℤ) else 0) +
    (if 39 = n then (-10905190400 : ℤ) else 0) +
    (if 40 = n then (-4194304000 : ℤ) else 0) +
    (if 41 = n then (19293798400 : ℤ) else 0) +
    (if 42 = n then (1495269376 : ℤ) else 0) +
    (if 43 = n then (-22284337152 : ℤ) else 0) +
    (if 44 = n then (2321285120 : ℤ) else 0) +
    (if 45 = n then (17641766912 : ℤ) else 0) +
    (if 46 = n then (-3931045888 : ℤ) else 0) +
    (if 47 = n then (-9779675136 : ℤ) else 0) +
    (if 48 = n then (2984706048 : ℤ) else 0) +
    (if 49 = n then (3810263040 : ℤ) else 0) +
    (if 50 = n then (-1389158400 : ℤ) else 0) +
    (if 51 = n then (-1031946240 : ℤ) else 0) +
    (if 52 = n then (421378048 : ℤ) else 0) +
    (if 53 = n then (189190144 : ℤ) else 0) +
    (if 54 = n then (-83393024 : ℤ) else 0) +
    (if 55 = n then (-22404096 : ℤ) else 0) +
    (if 56 = n then (10409984 : ℤ) else 0) +
    (if 57 = n then (1584128 : ℤ) else 0) +
    (if 58 = n then (-762944 : ℤ) else 0) +
    (if 59 = n then (-58240 : ℤ) else 0) +
    (if 60 = n then (28700 : ℤ) else 0) +
    (if 61 = n then (840 : ℤ) else 0) +
    (if 62 = n then (-419 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_33 (n : ℕ) :
    fixedRowDData_33.coeff n = fixedRowDCoeff_33 n := by
  simp only [fixedRowDData_33, fixedRowDCoeff_33, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_33 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_33 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_33, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_33 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_28 (k.val + 2) - 2 * fixedReversedUCoeff_28 (k.val + 1) + fixedReversedUCoeff_28 k.val) = fixedRowDCoeff_33 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_33 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_28 = fixedRowDData_33 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_28, fixed_rowD_typed_coeff_33]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_28, fixed_rowD_typed_coeff_33]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_28, fixed_rowD_typed_coeff_33]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_33 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_28 _ (by omega),
              fixed_reversedU_typed_tail_28 _ (by omega), fixed_reversedU_typed_tail_28 _ hn',
              fixed_rowD_typed_tail_33 _ (by omega)]
            decide

theorem fixed_rowD_typed_33 : rowD 1 33 = fixedRowDData_33 := by
  calc
    rowD 1 33 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_28 :=
      fixedTyped_rowD_of_parameters 1 33 2 63 28 (1)
        fixedChebyshevUData_28 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_28
    _ = fixedRowDData_33 := by
      rw [fixed_reversedU_typed_data_28, fixed_rowD_typed_factor_33]

end InternalCatalan

end

end

end OAI
