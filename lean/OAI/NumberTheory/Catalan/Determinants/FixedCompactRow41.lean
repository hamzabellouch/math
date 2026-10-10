import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT32To39
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU32To39

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_41 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 25 (68719476736 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-137438953472 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-566935683072 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (1271310319616 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (2065879269376 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-5403068858368 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-4290672328704 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (13984413515776 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (5323611963392 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-24631637442560 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-3309876281344 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (31251390005248 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-882095685632 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-29487198633984 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (4212456947712 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (21062284738560 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-4788946206720 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-11484392325120 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (3349614428160 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (4785163468800 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-1634930851840 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-1515301765120 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (577510113280 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (360281538560 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-148616134656 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-63049269248 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (27584055296 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (7881158656 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-3604039168 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-673080320 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (318183424 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (36713472 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-17783088 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-1147296 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (565212 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (16872 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-8399 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-74 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (37 : ℤ)

def fixedRowPCoeff_41 (n : ℕ) : ℤ :=
    (if 25 = n then (68719476736 : ℤ) else 0) +
    (if 26 = n then (-137438953472 : ℤ) else 0) +
    (if 27 = n then (-566935683072 : ℤ) else 0) +
    (if 28 = n then (1271310319616 : ℤ) else 0) +
    (if 29 = n then (2065879269376 : ℤ) else 0) +
    (if 30 = n then (-5403068858368 : ℤ) else 0) +
    (if 31 = n then (-4290672328704 : ℤ) else 0) +
    (if 32 = n then (13984413515776 : ℤ) else 0) +
    (if 33 = n then (5323611963392 : ℤ) else 0) +
    (if 34 = n then (-24631637442560 : ℤ) else 0) +
    (if 35 = n then (-3309876281344 : ℤ) else 0) +
    (if 36 = n then (31251390005248 : ℤ) else 0) +
    (if 37 = n then (-882095685632 : ℤ) else 0) +
    (if 38 = n then (-29487198633984 : ℤ) else 0) +
    (if 39 = n then (4212456947712 : ℤ) else 0) +
    (if 40 = n then (21062284738560 : ℤ) else 0) +
    (if 41 = n then (-4788946206720 : ℤ) else 0) +
    (if 42 = n then (-11484392325120 : ℤ) else 0) +
    (if 43 = n then (3349614428160 : ℤ) else 0) +
    (if 44 = n then (4785163468800 : ℤ) else 0) +
    (if 45 = n then (-1634930851840 : ℤ) else 0) +
    (if 46 = n then (-1515301765120 : ℤ) else 0) +
    (if 47 = n then (577510113280 : ℤ) else 0) +
    (if 48 = n then (360281538560 : ℤ) else 0) +
    (if 49 = n then (-148616134656 : ℤ) else 0) +
    (if 50 = n then (-63049269248 : ℤ) else 0) +
    (if 51 = n then (27584055296 : ℤ) else 0) +
    (if 52 = n then (7881158656 : ℤ) else 0) +
    (if 53 = n then (-3604039168 : ℤ) else 0) +
    (if 54 = n then (-673080320 : ℤ) else 0) +
    (if 55 = n then (318183424 : ℤ) else 0) +
    (if 56 = n then (36713472 : ℤ) else 0) +
    (if 57 = n then (-17783088 : ℤ) else 0) +
    (if 58 = n then (-1147296 : ℤ) else 0) +
    (if 59 = n then (565212 : ℤ) else 0) +
    (if 60 = n then (16872 : ℤ) else 0) +
    (if 61 = n then (-8399 : ℤ) else 0) +
    (if 62 = n then (-74 : ℤ) else 0) +
    (if 63 = n then (37 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_41 (n : ℕ) :
    fixedRowPData_41.coeff n = fixedRowPCoeff_41 n := by
  simp only [fixedRowPData_41, fixedRowPCoeff_41, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_41 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_41 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_41, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_41 : ∀ k : Fin 63,
    fixedReversedTCoeff_37 (k.val + 2) - 2 * fixedReversedTCoeff_37 (k.val + 1) + fixedReversedTCoeff_37 k.val = fixedRowPCoeff_41 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_41 :
    (1 - X) ^ 2 * fixedReversedTData_37 = fixedRowPData_41 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_37, fixed_rowP_typed_coeff_41]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_37, fixed_rowP_typed_coeff_41]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_37, fixed_rowP_typed_coeff_41]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_41 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_37 _ (by omega),
              fixed_reversedT_typed_tail_37 _ (by omega), fixed_reversedT_typed_tail_37 _ hn',
              fixed_rowP_typed_tail_41 _ (by omega)]
            decide

theorem fixed_rowP_typed_41 : rowP 1 41 = fixedRowPData_41 := by
  calc
    rowP 1 41 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_37 :=
      fixedTyped_rowP_of_parameters 1 41 2 63 37 fixedChebyshevTData_37
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_37
    _ = fixedRowPData_41 := by
      rw [fixed_reversedT_typed_data_37, fixed_rowP_typed_factor_41]

def fixedRowDData_41 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 26 (68719476736 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-137438953472 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-532575944704 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (1202590842880 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (1808181231616 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-4818953306112 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-3448858738688 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (11716670783488 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (3794603606016 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-19305877995520 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-1749595193344 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (22805068382208 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-1440642760704 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-19923782860800 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (3415505633280 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (13092771594240 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-3287301488640 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-6518168616960 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (2030461255680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (2457246105600 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-880513187840 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-696219729920 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (275079823360 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (146060083200 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-61953818624 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-22152445952 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (9904699392 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (2343047168 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-1089662464 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-163722240 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (78388224 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (6945792 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-3395376 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-155040 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (76836 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1368 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-683 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowDCoeff_41 (n : ℕ) : ℤ :=
    (if 26 = n then (68719476736 : ℤ) else 0) +
    (if 27 = n then (-137438953472 : ℤ) else 0) +
    (if 28 = n then (-532575944704 : ℤ) else 0) +
    (if 29 = n then (1202590842880 : ℤ) else 0) +
    (if 30 = n then (1808181231616 : ℤ) else 0) +
    (if 31 = n then (-4818953306112 : ℤ) else 0) +
    (if 32 = n then (-3448858738688 : ℤ) else 0) +
    (if 33 = n then (11716670783488 : ℤ) else 0) +
    (if 34 = n then (3794603606016 : ℤ) else 0) +
    (if 35 = n then (-19305877995520 : ℤ) else 0) +
    (if 36 = n then (-1749595193344 : ℤ) else 0) +
    (if 37 = n then (22805068382208 : ℤ) else 0) +
    (if 38 = n then (-1440642760704 : ℤ) else 0) +
    (if 39 = n then (-19923782860800 : ℤ) else 0) +
    (if 40 = n then (3415505633280 : ℤ) else 0) +
    (if 41 = n then (13092771594240 : ℤ) else 0) +
    (if 42 = n then (-3287301488640 : ℤ) else 0) +
    (if 43 = n then (-6518168616960 : ℤ) else 0) +
    (if 44 = n then (2030461255680 : ℤ) else 0) +
    (if 45 = n then (2457246105600 : ℤ) else 0) +
    (if 46 = n then (-880513187840 : ℤ) else 0) +
    (if 47 = n then (-696219729920 : ℤ) else 0) +
    (if 48 = n then (275079823360 : ℤ) else 0) +
    (if 49 = n then (146060083200 : ℤ) else 0) +
    (if 50 = n then (-61953818624 : ℤ) else 0) +
    (if 51 = n then (-22152445952 : ℤ) else 0) +
    (if 52 = n then (9904699392 : ℤ) else 0) +
    (if 53 = n then (2343047168 : ℤ) else 0) +
    (if 54 = n then (-1089662464 : ℤ) else 0) +
    (if 55 = n then (-163722240 : ℤ) else 0) +
    (if 56 = n then (78388224 : ℤ) else 0) +
    (if 57 = n then (6945792 : ℤ) else 0) +
    (if 58 = n then (-3395376 : ℤ) else 0) +
    (if 59 = n then (-155040 : ℤ) else 0) +
    (if 60 = n then (76836 : ℤ) else 0) +
    (if 61 = n then (1368 : ℤ) else 0) +
    (if 62 = n then (-683 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_41 (n : ℕ) :
    fixedRowDData_41.coeff n = fixedRowDCoeff_41 n := by
  simp only [fixedRowDData_41, fixedRowDCoeff_41, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_41 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_41 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_41, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_41 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_36 (k.val + 2) - 2 * fixedReversedUCoeff_36 (k.val + 1) + fixedReversedUCoeff_36 k.val) = fixedRowDCoeff_41 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_41 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_36 = fixedRowDData_41 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_36, fixed_rowD_typed_coeff_41]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_36, fixed_rowD_typed_coeff_41]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_36, fixed_rowD_typed_coeff_41]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_41 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_36 _ (by omega),
              fixed_reversedU_typed_tail_36 _ (by omega), fixed_reversedU_typed_tail_36 _ hn',
              fixed_rowD_typed_tail_41 _ (by omega)]
            decide

theorem fixed_rowD_typed_41 : rowD 1 41 = fixedRowDData_41 := by
  calc
    rowD 1 41 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_36 :=
      fixedTyped_rowD_of_parameters 1 41 2 63 36 (1)
        fixedChebyshevUData_36 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_36
    _ = fixedRowDData_41 := by
      rw [fixed_reversedU_typed_data_36, fixed_rowD_typed_factor_41]

end InternalCatalan

end

end

end OAI
