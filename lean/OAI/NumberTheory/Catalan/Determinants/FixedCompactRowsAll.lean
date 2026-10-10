import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow0
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow1
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow10
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow11
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow12
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow13
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow14
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow15
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow16
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow17
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow18
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow2
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow21
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow22
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow23
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow24
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow25
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow26
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow27
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow28
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow29
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow3
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow30
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow31
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow32
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow33
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow34
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow35
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow36
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow37
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow38
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow39
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow40
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow41
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow42
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow43
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow44
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow45
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow46
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow47
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow48
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow5
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow6
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow7
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow8
import OAI.NumberTheory.Catalan.Determinants.FixedCompactRow9

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_4 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_4 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_4 (n : ℕ) :
    fixedRowPData_4.coeff n = fixedRowPCoeff_4 n := by
  simp only [fixedRowPData_4, fixedRowPCoeff_4, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_4 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_4 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_4, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_4 : ∀ k : Fin 63,
    fixedReversedTCoeff_0 (k.val + 2) - 2 * fixedReversedTCoeff_0 (k.val + 1) + fixedReversedTCoeff_0 k.val = fixedRowPCoeff_4 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_4 :
    (1 - X) ^ 2 * fixedReversedTData_0 = fixedRowPData_4 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_0, fixed_rowP_typed_coeff_4]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_0, fixed_rowP_typed_coeff_4]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_0, fixed_rowP_typed_coeff_4]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_4 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_0 _ (by omega),
              fixed_reversedT_typed_tail_0 _ (by omega), fixed_reversedT_typed_tail_0 _ hn',
              fixed_rowP_typed_tail_4 _ (by omega)]
            decide

theorem fixed_rowP_typed_4 : rowP 1 4 = fixedRowPData_4 := by
  calc
    rowP 1 4 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_0 :=
      fixedTyped_rowP_of_parameters 1 4 2 63 0 fixedChebyshevTData_0
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_0
    _ = fixedRowPData_4 := by
      rw [fixed_reversedT_typed_data_0, fixed_rowP_typed_factor_4]

def fixedRowDData_4 : ℤ[X] :=
    0

def fixedRowDCoeff_4 (_n : ℕ) : ℤ :=
    0

theorem fixed_rowD_typed_coeff_4 (n : ℕ) :
    fixedRowDData_4.coeff n = fixedRowDCoeff_4 n := by
  simp only [fixedRowDData_4, fixedRowDCoeff_4, coeff_zero]

theorem fixed_rowD_typed_tail_4 (n : ℕ) (_hn : 65 ≤ n) :
    fixedRowDCoeff_4 n = 0 := by
  simp only [fixedRowDCoeff_4]

theorem fixed_rowD_typed_4 : rowD 1 4 = fixedRowDData_4 := by
  apply rowD_eq_zero_of_distance_zero
  decide

end InternalCatalan

end

end

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_19 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 47 (16384 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-32768 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-45056 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (122880 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (30720 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-184320 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (21760 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (140800 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-41600 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-57600 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (22752 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (12096 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-5488 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-1120 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (545 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (30 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-15 : ℤ)

def fixedRowPCoeff_19 (n : ℕ) : ℤ :=
    (if 47 = n then (16384 : ℤ) else 0) +
    (if 48 = n then (-32768 : ℤ) else 0) +
    (if 49 = n then (-45056 : ℤ) else 0) +
    (if 50 = n then (122880 : ℤ) else 0) +
    (if 51 = n then (30720 : ℤ) else 0) +
    (if 52 = n then (-184320 : ℤ) else 0) +
    (if 53 = n then (21760 : ℤ) else 0) +
    (if 54 = n then (140800 : ℤ) else 0) +
    (if 55 = n then (-41600 : ℤ) else 0) +
    (if 56 = n then (-57600 : ℤ) else 0) +
    (if 57 = n then (22752 : ℤ) else 0) +
    (if 58 = n then (12096 : ℤ) else 0) +
    (if 59 = n then (-5488 : ℤ) else 0) +
    (if 60 = n then (-1120 : ℤ) else 0) +
    (if 61 = n then (545 : ℤ) else 0) +
    (if 62 = n then (30 : ℤ) else 0) +
    (if 63 = n then (-15 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_19 (n : ℕ) :
    fixedRowPData_19.coeff n = fixedRowPCoeff_19 n := by
  simp only [fixedRowPData_19, fixedRowPCoeff_19, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_19 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_19 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_19, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_19 : ∀ k : Fin 63,
    fixedReversedTCoeff_15 (k.val + 2) - 2 * fixedReversedTCoeff_15 (k.val + 1) + fixedReversedTCoeff_15 k.val = fixedRowPCoeff_19 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_19 :
    (1 - X) ^ 2 * fixedReversedTData_15 = fixedRowPData_19 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_15, fixed_rowP_typed_coeff_19]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_15, fixed_rowP_typed_coeff_19]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_15, fixed_rowP_typed_coeff_19]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_19 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_15 _ (by omega),
              fixed_reversedT_typed_tail_15 _ (by omega), fixed_reversedT_typed_tail_15 _ hn',
              fixed_rowP_typed_tail_19 _ (by omega)]
            decide

theorem fixed_rowP_typed_19 : rowP 1 19 = fixedRowPData_19 := by
  calc
    rowP 1 19 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_15 :=
      fixedTyped_rowP_of_parameters 1 19 2 63 15 fixedChebyshevTData_15
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_15
    _ = fixedRowPData_19 := by
      rw [fixed_reversedT_typed_data_15, fixed_rowP_typed_factor_19]

def fixedRowDData_19 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 48 (16384 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-32768 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-36864 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (106496 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (14336 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-135168 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (25344 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (84480 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-28800 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-26880 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (11424 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (4032 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-1904 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-224 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (111 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_19 (n : ℕ) : ℤ :=
    (if 48 = n then (16384 : ℤ) else 0) +
    (if 49 = n then (-32768 : ℤ) else 0) +
    (if 50 = n then (-36864 : ℤ) else 0) +
    (if 51 = n then (106496 : ℤ) else 0) +
    (if 52 = n then (14336 : ℤ) else 0) +
    (if 53 = n then (-135168 : ℤ) else 0) +
    (if 54 = n then (25344 : ℤ) else 0) +
    (if 55 = n then (84480 : ℤ) else 0) +
    (if 56 = n then (-28800 : ℤ) else 0) +
    (if 57 = n then (-26880 : ℤ) else 0) +
    (if 58 = n then (11424 : ℤ) else 0) +
    (if 59 = n then (4032 : ℤ) else 0) +
    (if 60 = n then (-1904 : ℤ) else 0) +
    (if 61 = n then (-224 : ℤ) else 0) +
    (if 62 = n then (111 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_19 (n : ℕ) :
    fixedRowDData_19.coeff n = fixedRowDCoeff_19 n := by
  simp only [fixedRowDData_19, fixedRowDCoeff_19, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_19 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_19 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_19, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_19 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_14 (k.val + 2) - 2 * fixedReversedUCoeff_14 (k.val + 1) + fixedReversedUCoeff_14 k.val) = fixedRowDCoeff_19 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_19 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_14 = fixedRowDData_19 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_14, fixed_rowD_typed_coeff_19]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_14, fixed_rowD_typed_coeff_19]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_14, fixed_rowD_typed_coeff_19]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_19 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_14 _ (by omega),
              fixed_reversedU_typed_tail_14 _ (by omega), fixed_reversedU_typed_tail_14 _ hn',
              fixed_rowD_typed_tail_19 _ (by omega)]
            decide

theorem fixed_rowD_typed_19 : rowD 1 19 = fixedRowDData_19 := by
  calc
    rowD 1 19 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_14 :=
      fixedTyped_rowD_of_parameters 1 19 2 63 14 (1)
        fixedChebyshevUData_14 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_14
    _ = fixedRowDData_19 := by
      rw [fixed_reversedU_typed_data_14, fixed_rowD_typed_factor_19]

end InternalCatalan

end

end

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_20 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 46 (32768 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-65536 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-98304 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (262144 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (81920 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-425984 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (32768 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (360448 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-95744 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-168960 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (62976 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (43008 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-18816 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-5376 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (2560 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (256 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-127 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_20 (n : ℕ) : ℤ :=
    (if 46 = n then (32768 : ℤ) else 0) +
    (if 47 = n then (-65536 : ℤ) else 0) +
    (if 48 = n then (-98304 : ℤ) else 0) +
    (if 49 = n then (262144 : ℤ) else 0) +
    (if 50 = n then (81920 : ℤ) else 0) +
    (if 51 = n then (-425984 : ℤ) else 0) +
    (if 52 = n then (32768 : ℤ) else 0) +
    (if 53 = n then (360448 : ℤ) else 0) +
    (if 54 = n then (-95744 : ℤ) else 0) +
    (if 55 = n then (-168960 : ℤ) else 0) +
    (if 56 = n then (62976 : ℤ) else 0) +
    (if 57 = n then (43008 : ℤ) else 0) +
    (if 58 = n then (-18816 : ℤ) else 0) +
    (if 59 = n then (-5376 : ℤ) else 0) +
    (if 60 = n then (2560 : ℤ) else 0) +
    (if 61 = n then (256 : ℤ) else 0) +
    (if 62 = n then (-127 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_20 (n : ℕ) :
    fixedRowPData_20.coeff n = fixedRowPCoeff_20 n := by
  simp only [fixedRowPData_20, fixedRowPCoeff_20, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_20 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_20 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_20, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_20 : ∀ k : Fin 63,
    fixedReversedTCoeff_16 (k.val + 2) - 2 * fixedReversedTCoeff_16 (k.val + 1) + fixedReversedTCoeff_16 k.val = fixedRowPCoeff_20 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_20 :
    (1 - X) ^ 2 * fixedReversedTData_16 = fixedRowPData_20 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_16, fixed_rowP_typed_coeff_20]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_16, fixed_rowP_typed_coeff_20]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_16, fixed_rowP_typed_coeff_20]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_20 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_16 _ (by omega),
              fixed_reversedT_typed_tail_16 _ (by omega), fixed_reversedT_typed_tail_16 _ hn',
              fixed_rowP_typed_tail_20 _ (by omega)]
            decide

theorem fixed_rowP_typed_20 : rowP 1 20 = fixedRowPData_20 := by
  calc
    rowP 1 20 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_16 :=
      fixedTyped_rowP_of_parameters 1 20 2 63 16 fixedChebyshevTData_16
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_16
    _ = fixedRowPData_20 := by
      rw [fixed_reversedT_typed_data_16, fixed_rowP_typed_factor_20]

def fixedRowDData_20 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 47 (32768 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-65536 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-81920 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (229376 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (45056 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-319488 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (47104 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (225280 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-70400 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-84480 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (34176 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (16128 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-7392 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-1344 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (656 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (32 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-16 : ℤ)

def fixedRowDCoeff_20 (n : ℕ) : ℤ :=
    (if 47 = n then (32768 : ℤ) else 0) +
    (if 48 = n then (-65536 : ℤ) else 0) +
    (if 49 = n then (-81920 : ℤ) else 0) +
    (if 50 = n then (229376 : ℤ) else 0) +
    (if 51 = n then (45056 : ℤ) else 0) +
    (if 52 = n then (-319488 : ℤ) else 0) +
    (if 53 = n then (47104 : ℤ) else 0) +
    (if 54 = n then (225280 : ℤ) else 0) +
    (if 55 = n then (-70400 : ℤ) else 0) +
    (if 56 = n then (-84480 : ℤ) else 0) +
    (if 57 = n then (34176 : ℤ) else 0) +
    (if 58 = n then (16128 : ℤ) else 0) +
    (if 59 = n then (-7392 : ℤ) else 0) +
    (if 60 = n then (-1344 : ℤ) else 0) +
    (if 61 = n then (656 : ℤ) else 0) +
    (if 62 = n then (32 : ℤ) else 0) +
    (if 63 = n then (-16 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_20 (n : ℕ) :
    fixedRowDData_20.coeff n = fixedRowDCoeff_20 n := by
  simp only [fixedRowDData_20, fixedRowDCoeff_20, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_20 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_20 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_20, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_20 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_15 (k.val + 2) - 2 * fixedReversedUCoeff_15 (k.val + 1) + fixedReversedUCoeff_15 k.val) = fixedRowDCoeff_20 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_20 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_15 = fixedRowDData_20 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_15, fixed_rowD_typed_coeff_20]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_15, fixed_rowD_typed_coeff_20]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_15, fixed_rowD_typed_coeff_20]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_20 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_15 _ (by omega),
              fixed_reversedU_typed_tail_15 _ (by omega), fixed_reversedU_typed_tail_15 _ hn',
              fixed_rowD_typed_tail_20 _ (by omega)]
            decide

theorem fixed_rowD_typed_20 : rowD 1 20 = fixedRowDData_20 := by
  calc
    rowD 1 20 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_15 :=
      fixedTyped_rowD_of_parameters 1 20 2 63 15 (1)
        fixedChebyshevUData_15 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_15
    _ = fixedRowDData_20 := by
      rw [fixed_reversedU_typed_data_15, fixed_rowD_typed_factor_20]

end InternalCatalan

end

end

section



end

end OAI
