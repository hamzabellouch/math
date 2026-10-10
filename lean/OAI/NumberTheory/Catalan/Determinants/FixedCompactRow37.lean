import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT32To39
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU32To39

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_37 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 29 (4294967296 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-8589934592 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-31138512896 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (70866960384 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (97442070528 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-265751101440 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-166832635904 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (599416373248 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (153729630208 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-906875633664 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-32388415488 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (971652464640 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-106461921280 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-758728622080 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (160500285440 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (437728051200 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-125299654656 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-187128741888 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (64108920832 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (58910900224 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-22731923456 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-13447053312 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (5639983104 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (2167087104 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-965299712 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-236487680 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (110057728 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (16372224 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-7862976 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-646272 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (317152 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (11968 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-5951 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-66 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (33 : ℤ)

def fixedRowPCoeff_37 (n : ℕ) : ℤ :=
    (if 29 = n then (4294967296 : ℤ) else 0) +
    (if 30 = n then (-8589934592 : ℤ) else 0) +
    (if 31 = n then (-31138512896 : ℤ) else 0) +
    (if 32 = n then (70866960384 : ℤ) else 0) +
    (if 33 = n then (97442070528 : ℤ) else 0) +
    (if 34 = n then (-265751101440 : ℤ) else 0) +
    (if 35 = n then (-166832635904 : ℤ) else 0) +
    (if 36 = n then (599416373248 : ℤ) else 0) +
    (if 37 = n then (153729630208 : ℤ) else 0) +
    (if 38 = n then (-906875633664 : ℤ) else 0) +
    (if 39 = n then (-32388415488 : ℤ) else 0) +
    (if 40 = n then (971652464640 : ℤ) else 0) +
    (if 41 = n then (-106461921280 : ℤ) else 0) +
    (if 42 = n then (-758728622080 : ℤ) else 0) +
    (if 43 = n then (160500285440 : ℤ) else 0) +
    (if 44 = n then (437728051200 : ℤ) else 0) +
    (if 45 = n then (-125299654656 : ℤ) else 0) +
    (if 46 = n then (-187128741888 : ℤ) else 0) +
    (if 47 = n then (64108920832 : ℤ) else 0) +
    (if 48 = n then (58910900224 : ℤ) else 0) +
    (if 49 = n then (-22731923456 : ℤ) else 0) +
    (if 50 = n then (-13447053312 : ℤ) else 0) +
    (if 51 = n then (5639983104 : ℤ) else 0) +
    (if 52 = n then (2167087104 : ℤ) else 0) +
    (if 53 = n then (-965299712 : ℤ) else 0) +
    (if 54 = n then (-236487680 : ℤ) else 0) +
    (if 55 = n then (110057728 : ℤ) else 0) +
    (if 56 = n then (16372224 : ℤ) else 0) +
    (if 57 = n then (-7862976 : ℤ) else 0) +
    (if 58 = n then (-646272 : ℤ) else 0) +
    (if 59 = n then (317152 : ℤ) else 0) +
    (if 60 = n then (11968 : ℤ) else 0) +
    (if 61 = n then (-5951 : ℤ) else 0) +
    (if 62 = n then (-66 : ℤ) else 0) +
    (if 63 = n then (33 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_37 (n : ℕ) :
    fixedRowPData_37.coeff n = fixedRowPCoeff_37 n := by
  simp only [fixedRowPData_37, fixedRowPCoeff_37, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_37 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_37 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_37, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_37 : ∀ k : Fin 63,
    fixedReversedTCoeff_33 (k.val + 2) - 2 * fixedReversedTCoeff_33 (k.val + 1) + fixedReversedTCoeff_33 k.val = fixedRowPCoeff_37 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_37 :
    (1 - X) ^ 2 * fixedReversedTData_33 = fixedRowPData_37 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_33, fixed_rowP_typed_coeff_37]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_33, fixed_rowP_typed_coeff_37]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_33, fixed_rowP_typed_coeff_37]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_37 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_33 _ (by omega),
              fixed_reversedT_typed_tail_33 _ (by omega), fixed_reversedT_typed_tail_33 _ hn',
              fixed_rowP_typed_tail_37 _ (by omega)]
            decide

theorem fixed_rowP_typed_37 : rowP 1 37 = fixedRowPData_37 := by
  calc
    rowP 1 37 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_33 :=
      fixedTyped_rowP_of_parameters 1 37 2 63 33 fixedChebyshevTData_33
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_33
    _ = fixedRowPData_37 := by
      rw [fixed_reversedT_typed_data_33, fixed_rowP_typed_factor_37]

def fixedRowDData_37 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 30 (4294967296 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-8589934592 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-28991029248 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (66571993088 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (83483426816 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-233538846720 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-128446365696 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (490431578112 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (98297708544 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-687026995200 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (4907335680 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (677212323840 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-97192509440 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-482827304960 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (115401031680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (252025241600 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-77812793344 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-96399654912 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (34810986496 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (26777681920 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-10740178944 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-5297324032 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (2287480832 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (722362368 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-328932864 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-64496640 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (30511872 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (3472896 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-1687488 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-97920 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (48416 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1088 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-543 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_37 (n : ℕ) : ℤ :=
    (if 30 = n then (4294967296 : ℤ) else 0) +
    (if 31 = n then (-8589934592 : ℤ) else 0) +
    (if 32 = n then (-28991029248 : ℤ) else 0) +
    (if 33 = n then (66571993088 : ℤ) else 0) +
    (if 34 = n then (83483426816 : ℤ) else 0) +
    (if 35 = n then (-233538846720 : ℤ) else 0) +
    (if 36 = n then (-128446365696 : ℤ) else 0) +
    (if 37 = n then (490431578112 : ℤ) else 0) +
    (if 38 = n then (98297708544 : ℤ) else 0) +
    (if 39 = n then (-687026995200 : ℤ) else 0) +
    (if 40 = n then (4907335680 : ℤ) else 0) +
    (if 41 = n then (677212323840 : ℤ) else 0) +
    (if 42 = n then (-97192509440 : ℤ) else 0) +
    (if 43 = n then (-482827304960 : ℤ) else 0) +
    (if 44 = n then (115401031680 : ℤ) else 0) +
    (if 45 = n then (252025241600 : ℤ) else 0) +
    (if 46 = n then (-77812793344 : ℤ) else 0) +
    (if 47 = n then (-96399654912 : ℤ) else 0) +
    (if 48 = n then (34810986496 : ℤ) else 0) +
    (if 49 = n then (26777681920 : ℤ) else 0) +
    (if 50 = n then (-10740178944 : ℤ) else 0) +
    (if 51 = n then (-5297324032 : ℤ) else 0) +
    (if 52 = n then (2287480832 : ℤ) else 0) +
    (if 53 = n then (722362368 : ℤ) else 0) +
    (if 54 = n then (-328932864 : ℤ) else 0) +
    (if 55 = n then (-64496640 : ℤ) else 0) +
    (if 56 = n then (30511872 : ℤ) else 0) +
    (if 57 = n then (3472896 : ℤ) else 0) +
    (if 58 = n then (-1687488 : ℤ) else 0) +
    (if 59 = n then (-97920 : ℤ) else 0) +
    (if 60 = n then (48416 : ℤ) else 0) +
    (if 61 = n then (1088 : ℤ) else 0) +
    (if 62 = n then (-543 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_37 (n : ℕ) :
    fixedRowDData_37.coeff n = fixedRowDCoeff_37 n := by
  simp only [fixedRowDData_37, fixedRowDCoeff_37, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_37 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_37 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_37, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_37 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_32 (k.val + 2) - 2 * fixedReversedUCoeff_32 (k.val + 1) + fixedReversedUCoeff_32 k.val) = fixedRowDCoeff_37 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_37 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_32 = fixedRowDData_37 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_32, fixed_rowD_typed_coeff_37]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_32, fixed_rowD_typed_coeff_37]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_32, fixed_rowD_typed_coeff_37]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_37 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_32 _ (by omega),
              fixed_reversedU_typed_tail_32 _ (by omega), fixed_reversedU_typed_tail_32 _ hn',
              fixed_rowD_typed_tail_37 _ (by omega)]
            decide

theorem fixed_rowD_typed_37 : rowD 1 37 = fixedRowDData_37 := by
  calc
    rowD 1 37 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_32 :=
      fixedTyped_rowD_of_parameters 1 37 2 63 32 (1)
        fixedChebyshevUData_32 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_32
    _ = fixedRowDData_37 := by
      rw [fixed_reversedU_typed_data_32, fixed_rowD_typed_factor_37]

end InternalCatalan

end

end

end OAI
