import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT24To31
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU16To23

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_28 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 38 (8388608 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-16777216 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-41943040 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (100663296 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (81788928 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-264241152 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-67108864 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (398458880 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-8716288 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-381026304 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (70189056 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (240648192 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-69632000 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-101384192 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (36634624 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (28114944 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-11586432 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-4942080 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (2214784 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (512512 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-242528 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-27456 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (13440 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (576 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-287 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_28 (n : ℕ) : ℤ :=
    (if 38 = n then (8388608 : ℤ) else 0) +
    (if 39 = n then (-16777216 : ℤ) else 0) +
    (if 40 = n then (-41943040 : ℤ) else 0) +
    (if 41 = n then (100663296 : ℤ) else 0) +
    (if 42 = n then (81788928 : ℤ) else 0) +
    (if 43 = n then (-264241152 : ℤ) else 0) +
    (if 44 = n then (-67108864 : ℤ) else 0) +
    (if 45 = n then (398458880 : ℤ) else 0) +
    (if 46 = n then (-8716288 : ℤ) else 0) +
    (if 47 = n then (-381026304 : ℤ) else 0) +
    (if 48 = n then (70189056 : ℤ) else 0) +
    (if 49 = n then (240648192 : ℤ) else 0) +
    (if 50 = n then (-69632000 : ℤ) else 0) +
    (if 51 = n then (-101384192 : ℤ) else 0) +
    (if 52 = n then (36634624 : ℤ) else 0) +
    (if 53 = n then (28114944 : ℤ) else 0) +
    (if 54 = n then (-11586432 : ℤ) else 0) +
    (if 55 = n then (-4942080 : ℤ) else 0) +
    (if 56 = n then (2214784 : ℤ) else 0) +
    (if 57 = n then (512512 : ℤ) else 0) +
    (if 58 = n then (-242528 : ℤ) else 0) +
    (if 59 = n then (-27456 : ℤ) else 0) +
    (if 60 = n then (13440 : ℤ) else 0) +
    (if 61 = n then (576 : ℤ) else 0) +
    (if 62 = n then (-287 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_28 (n : ℕ) :
    fixedRowPData_28.coeff n = fixedRowPCoeff_28 n := by
  simp only [fixedRowPData_28, fixedRowPCoeff_28, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_28 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_28 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_28, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_28 : ∀ k : Fin 63,
    fixedReversedTCoeff_24 (k.val + 2) - 2 * fixedReversedTCoeff_24 (k.val + 1) + fixedReversedTCoeff_24 k.val = fixedRowPCoeff_28 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_28 :
    (1 - X) ^ 2 * fixedReversedTData_24 = fixedRowPData_28 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_24, fixed_rowP_typed_coeff_28]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_24, fixed_rowP_typed_coeff_28]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_24, fixed_rowP_typed_coeff_28]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_28 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_24 _ (by omega),
              fixed_reversedT_typed_tail_24 _ (by omega), fixed_reversedT_typed_tail_24 _ hn',
              fixed_rowP_typed_tail_28 _ (by omega)]
            decide

theorem fixed_rowP_typed_28 : rowP 1 28 = fixedRowPData_28 := by
  calc
    rowP 1 28 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_24 :=
      fixedTyped_rowP_of_parameters 1 28 2 63 24 fixedChebyshevTData_24
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_24
    _ = fixedRowPData_28 := by
      rw [fixed_reversedT_typed_data_24, fixed_rowP_typed_factor_28]

def fixedRowDData_28 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 39 (8388608 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-16777216 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-37748736 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (92274688 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (63963136 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-220200960 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-39321600 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (298844160 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-22413312 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-254017536 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (56819712 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (140378112 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-44843008 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-50692096 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (19488768 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (11714560 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-5033600 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-1647360 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (759616 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (128128 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-61776 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-4576 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (2264 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (48 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-24 : ℤ)

def fixedRowDCoeff_28 (n : ℕ) : ℤ :=
    (if 39 = n then (8388608 : ℤ) else 0) +
    (if 40 = n then (-16777216 : ℤ) else 0) +
    (if 41 = n then (-37748736 : ℤ) else 0) +
    (if 42 = n then (92274688 : ℤ) else 0) +
    (if 43 = n then (63963136 : ℤ) else 0) +
    (if 44 = n then (-220200960 : ℤ) else 0) +
    (if 45 = n then (-39321600 : ℤ) else 0) +
    (if 46 = n then (298844160 : ℤ) else 0) +
    (if 47 = n then (-22413312 : ℤ) else 0) +
    (if 48 = n then (-254017536 : ℤ) else 0) +
    (if 49 = n then (56819712 : ℤ) else 0) +
    (if 50 = n then (140378112 : ℤ) else 0) +
    (if 51 = n then (-44843008 : ℤ) else 0) +
    (if 52 = n then (-50692096 : ℤ) else 0) +
    (if 53 = n then (19488768 : ℤ) else 0) +
    (if 54 = n then (11714560 : ℤ) else 0) +
    (if 55 = n then (-5033600 : ℤ) else 0) +
    (if 56 = n then (-1647360 : ℤ) else 0) +
    (if 57 = n then (759616 : ℤ) else 0) +
    (if 58 = n then (128128 : ℤ) else 0) +
    (if 59 = n then (-61776 : ℤ) else 0) +
    (if 60 = n then (-4576 : ℤ) else 0) +
    (if 61 = n then (2264 : ℤ) else 0) +
    (if 62 = n then (48 : ℤ) else 0) +
    (if 63 = n then (-24 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_28 (n : ℕ) :
    fixedRowDData_28.coeff n = fixedRowDCoeff_28 n := by
  simp only [fixedRowDData_28, fixedRowDCoeff_28, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_28 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_28 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_28, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_28 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_23 (k.val + 2) - 2 * fixedReversedUCoeff_23 (k.val + 1) + fixedReversedUCoeff_23 k.val) = fixedRowDCoeff_28 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_28 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_23 = fixedRowDData_28 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_23, fixed_rowD_typed_coeff_28]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_23, fixed_rowD_typed_coeff_28]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_23, fixed_rowD_typed_coeff_28]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_28 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_23 _ (by omega),
              fixed_reversedU_typed_tail_23 _ (by omega), fixed_reversedU_typed_tail_23 _ hn',
              fixed_rowD_typed_tail_28 _ (by omega)]
            decide

theorem fixed_rowD_typed_28 : rowD 1 28 = fixedRowDData_28 := by
  calc
    rowD 1 28 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_23 :=
      fixedTyped_rowD_of_parameters 1 28 2 63 23 (1)
        fixedChebyshevUData_23 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_23
    _ = fixedRowDData_28 := by
      rw [fixed_reversedU_typed_data_23, fixed_rowD_typed_factor_28]

end InternalCatalan

end

end

end OAI
