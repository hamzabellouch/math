import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT16To23
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU16To23

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_26 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 40 (2097152 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-4194304 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-9437184 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (23068672 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (15859712 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-54788096 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-9371648 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (73531392 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-6127616 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-61276160 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (14237696 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (32800768 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-10762752 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-11275264 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (4429568 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (2416128 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-1057056 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-302016 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (141328 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (19360 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-9438 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-484 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (241 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowPCoeff_26 (n : ℕ) : ℤ :=
    (if 40 = n then (2097152 : ℤ) else 0) +
    (if 41 = n then (-4194304 : ℤ) else 0) +
    (if 42 = n then (-9437184 : ℤ) else 0) +
    (if 43 = n then (23068672 : ℤ) else 0) +
    (if 44 = n then (15859712 : ℤ) else 0) +
    (if 45 = n then (-54788096 : ℤ) else 0) +
    (if 46 = n then (-9371648 : ℤ) else 0) +
    (if 47 = n then (73531392 : ℤ) else 0) +
    (if 48 = n then (-6127616 : ℤ) else 0) +
    (if 49 = n then (-61276160 : ℤ) else 0) +
    (if 50 = n then (14237696 : ℤ) else 0) +
    (if 51 = n then (32800768 : ℤ) else 0) +
    (if 52 = n then (-10762752 : ℤ) else 0) +
    (if 53 = n then (-11275264 : ℤ) else 0) +
    (if 54 = n then (4429568 : ℤ) else 0) +
    (if 55 = n then (2416128 : ℤ) else 0) +
    (if 56 = n then (-1057056 : ℤ) else 0) +
    (if 57 = n then (-302016 : ℤ) else 0) +
    (if 58 = n then (141328 : ℤ) else 0) +
    (if 59 = n then (19360 : ℤ) else 0) +
    (if 60 = n then (-9438 : ℤ) else 0) +
    (if 61 = n then (-484 : ℤ) else 0) +
    (if 62 = n then (241 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_26 (n : ℕ) :
    fixedRowPData_26.coeff n = fixedRowPCoeff_26 n := by
  simp only [fixedRowPData_26, fixedRowPCoeff_26, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_26 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_26 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_26, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_26 : ∀ k : Fin 63,
    fixedReversedTCoeff_22 (k.val + 2) - 2 * fixedReversedTCoeff_22 (k.val + 1) + fixedReversedTCoeff_22 k.val = fixedRowPCoeff_26 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_26 :
    (1 - X) ^ 2 * fixedReversedTData_22 = fixedRowPData_26 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_22, fixed_rowP_typed_coeff_26]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_22, fixed_rowP_typed_coeff_26]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_22, fixed_rowP_typed_coeff_26]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_26 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_22 _ (by omega),
              fixed_reversedT_typed_tail_22 _ (by omega), fixed_reversedT_typed_tail_22 _ hn',
              fixed_rowP_typed_tail_26 _ (by omega)]
            decide

theorem fixed_rowP_typed_26 : rowP 1 26 = fixedRowPData_26 := by
  calc
    rowP 1 26 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_22 :=
      fixedTyped_rowP_of_parameters 1 26 2 63 22 fixedChebyshevTData_22
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_22
    _ = fixedRowPData_26 := by
      rw [fixed_reversedT_typed_data_22, fixed_rowP_typed_factor_26]

def fixedRowDData_26 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 41 (2097152 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-4194304 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-8388608 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (20971520 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (11927552 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-44826624 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-4325376 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (53477376 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-7241728 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-38993920 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (10551296 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (17891328 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-6383104 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-5125120 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (2123264 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (878592 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-398112 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-82368 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (39424 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (3520 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-1738 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-44 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (22 : ℤ)

def fixedRowDCoeff_26 (n : ℕ) : ℤ :=
    (if 41 = n then (2097152 : ℤ) else 0) +
    (if 42 = n then (-4194304 : ℤ) else 0) +
    (if 43 = n then (-8388608 : ℤ) else 0) +
    (if 44 = n then (20971520 : ℤ) else 0) +
    (if 45 = n then (11927552 : ℤ) else 0) +
    (if 46 = n then (-44826624 : ℤ) else 0) +
    (if 47 = n then (-4325376 : ℤ) else 0) +
    (if 48 = n then (53477376 : ℤ) else 0) +
    (if 49 = n then (-7241728 : ℤ) else 0) +
    (if 50 = n then (-38993920 : ℤ) else 0) +
    (if 51 = n then (10551296 : ℤ) else 0) +
    (if 52 = n then (17891328 : ℤ) else 0) +
    (if 53 = n then (-6383104 : ℤ) else 0) +
    (if 54 = n then (-5125120 : ℤ) else 0) +
    (if 55 = n then (2123264 : ℤ) else 0) +
    (if 56 = n then (878592 : ℤ) else 0) +
    (if 57 = n then (-398112 : ℤ) else 0) +
    (if 58 = n then (-82368 : ℤ) else 0) +
    (if 59 = n then (39424 : ℤ) else 0) +
    (if 60 = n then (3520 : ℤ) else 0) +
    (if 61 = n then (-1738 : ℤ) else 0) +
    (if 62 = n then (-44 : ℤ) else 0) +
    (if 63 = n then (22 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_26 (n : ℕ) :
    fixedRowDData_26.coeff n = fixedRowDCoeff_26 n := by
  simp only [fixedRowDData_26, fixedRowDCoeff_26, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_26 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_26 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_26, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_26 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_21 (k.val + 2) - 2 * fixedReversedUCoeff_21 (k.val + 1) + fixedReversedUCoeff_21 k.val) = fixedRowDCoeff_26 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_26 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_21 = fixedRowDData_26 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_21, fixed_rowD_typed_coeff_26]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_21, fixed_rowD_typed_coeff_26]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_21, fixed_rowD_typed_coeff_26]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_26 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_21 _ (by omega),
              fixed_reversedU_typed_tail_21 _ (by omega), fixed_reversedU_typed_tail_21 _ hn',
              fixed_rowD_typed_tail_26 _ (by omega)]
            decide

theorem fixed_rowD_typed_26 : rowD 1 26 = fixedRowDData_26 := by
  calc
    rowD 1 26 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_21 :=
      fixedTyped_rowD_of_parameters 1 26 2 63 21 (1)
        fixedChebyshevUData_21 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_21
    _ = fixedRowDData_26 := by
      rw [fixed_reversedU_typed_data_21, fixed_rowD_typed_factor_26]

end InternalCatalan

end

end

end OAI
