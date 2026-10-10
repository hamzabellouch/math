import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT16To23
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU16To23

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_27 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 39 (4194304 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-8388608 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-19922944 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (48234496 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (36175872 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-120586240 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-25624576 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (171835392 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-9043968 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-153747456 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (32030720 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (89686016 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-27697152 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-34291712 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (12935936 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (8419840 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-3578432 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-1262976 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (578864 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (105248 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-50600 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-4048 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (2001 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (46 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-23 : ℤ)

def fixedRowPCoeff_27 (n : ℕ) : ℤ :=
    (if 39 = n then (4194304 : ℤ) else 0) +
    (if 40 = n then (-8388608 : ℤ) else 0) +
    (if 41 = n then (-19922944 : ℤ) else 0) +
    (if 42 = n then (48234496 : ℤ) else 0) +
    (if 43 = n then (36175872 : ℤ) else 0) +
    (if 44 = n then (-120586240 : ℤ) else 0) +
    (if 45 = n then (-25624576 : ℤ) else 0) +
    (if 46 = n then (171835392 : ℤ) else 0) +
    (if 47 = n then (-9043968 : ℤ) else 0) +
    (if 48 = n then (-153747456 : ℤ) else 0) +
    (if 49 = n then (32030720 : ℤ) else 0) +
    (if 50 = n then (89686016 : ℤ) else 0) +
    (if 51 = n then (-27697152 : ℤ) else 0) +
    (if 52 = n then (-34291712 : ℤ) else 0) +
    (if 53 = n then (12935936 : ℤ) else 0) +
    (if 54 = n then (8419840 : ℤ) else 0) +
    (if 55 = n then (-3578432 : ℤ) else 0) +
    (if 56 = n then (-1262976 : ℤ) else 0) +
    (if 57 = n then (578864 : ℤ) else 0) +
    (if 58 = n then (105248 : ℤ) else 0) +
    (if 59 = n then (-50600 : ℤ) else 0) +
    (if 60 = n then (-4048 : ℤ) else 0) +
    (if 61 = n then (2001 : ℤ) else 0) +
    (if 62 = n then (46 : ℤ) else 0) +
    (if 63 = n then (-23 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_27 (n : ℕ) :
    fixedRowPData_27.coeff n = fixedRowPCoeff_27 n := by
  simp only [fixedRowPData_27, fixedRowPCoeff_27, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_27 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_27 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_27, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_27 : ∀ k : Fin 63,
    fixedReversedTCoeff_23 (k.val + 2) - 2 * fixedReversedTCoeff_23 (k.val + 1) + fixedReversedTCoeff_23 k.val = fixedRowPCoeff_27 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_27 :
    (1 - X) ^ 2 * fixedReversedTData_23 = fixedRowPData_27 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_23, fixed_rowP_typed_coeff_27]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_23, fixed_rowP_typed_coeff_27]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_23, fixed_rowP_typed_coeff_27]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_27 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_23 _ (by omega),
              fixed_reversedT_typed_tail_23 _ (by omega), fixed_reversedT_typed_tail_23 _ hn',
              fixed_rowP_typed_tail_27 _ (by omega)]
            decide

theorem fixed_rowP_typed_27 : rowP 1 27 = fixedRowPData_27 := by
  calc
    rowP 1 27 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_23 :=
      fixedTyped_rowP_of_parameters 1 27 2 63 23 fixedChebyshevTData_23
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_23
    _ = fixedRowPData_27 := by
      rw [fixed_reversedT_typed_data_23, fixed_rowP_typed_factor_27]

def fixedRowDData_27 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 40 (4194304 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-8388608 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-17825792 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (44040192 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (27787264 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-99614720 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-13697024 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (127008768 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-13369344 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-100270080 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (24788992 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (50692096 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-17145856 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-16400384 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (6552832 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (3294720 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-1455168 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-384384 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (180752 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (22880 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-11176 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-528 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (263 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_27 (n : ℕ) : ℤ :=
    (if 40 = n then (4194304 : ℤ) else 0) +
    (if 41 = n then (-8388608 : ℤ) else 0) +
    (if 42 = n then (-17825792 : ℤ) else 0) +
    (if 43 = n then (44040192 : ℤ) else 0) +
    (if 44 = n then (27787264 : ℤ) else 0) +
    (if 45 = n then (-99614720 : ℤ) else 0) +
    (if 46 = n then (-13697024 : ℤ) else 0) +
    (if 47 = n then (127008768 : ℤ) else 0) +
    (if 48 = n then (-13369344 : ℤ) else 0) +
    (if 49 = n then (-100270080 : ℤ) else 0) +
    (if 50 = n then (24788992 : ℤ) else 0) +
    (if 51 = n then (50692096 : ℤ) else 0) +
    (if 52 = n then (-17145856 : ℤ) else 0) +
    (if 53 = n then (-16400384 : ℤ) else 0) +
    (if 54 = n then (6552832 : ℤ) else 0) +
    (if 55 = n then (3294720 : ℤ) else 0) +
    (if 56 = n then (-1455168 : ℤ) else 0) +
    (if 57 = n then (-384384 : ℤ) else 0) +
    (if 58 = n then (180752 : ℤ) else 0) +
    (if 59 = n then (22880 : ℤ) else 0) +
    (if 60 = n then (-11176 : ℤ) else 0) +
    (if 61 = n then (-528 : ℤ) else 0) +
    (if 62 = n then (263 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_27 (n : ℕ) :
    fixedRowDData_27.coeff n = fixedRowDCoeff_27 n := by
  simp only [fixedRowDData_27, fixedRowDCoeff_27, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_27 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_27 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_27, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_27 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_22 (k.val + 2) - 2 * fixedReversedUCoeff_22 (k.val + 1) + fixedReversedUCoeff_22 k.val) = fixedRowDCoeff_27 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_27 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_22 = fixedRowDData_27 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_22, fixed_rowD_typed_coeff_27]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_22, fixed_rowD_typed_coeff_27]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_22, fixed_rowD_typed_coeff_27]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_27 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_22 _ (by omega),
              fixed_reversedU_typed_tail_22 _ (by omega), fixed_reversedU_typed_tail_22 _ hn',
              fixed_rowD_typed_tail_27 _ (by omega)]
            decide

theorem fixed_rowD_typed_27 : rowD 1 27 = fixedRowDData_27 := by
  calc
    rowD 1 27 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_22 :=
      fixedTyped_rowD_of_parameters 1 27 2 63 22 (1)
        fixedChebyshevUData_22 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_22
    _ = fixedRowDData_27 := by
      rw [fixed_reversedU_typed_data_22, fixed_rowD_typed_factor_27]

end InternalCatalan

end

end

end OAI
