import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT32To39
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU24To31

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_36 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 30 (2147483648 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-4294967296 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-15032385536 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (34359738368 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (45097156608 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-124554051584 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-73014444032 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (270582939648 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (61001957376 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-392586854400 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-4362076160 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (401311006720 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-52093255680 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-297124495360 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (67914170368 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (161296154624 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-48514859008 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-64266436608 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (22819241984 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (18627952640 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-7387676672 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-3852599296 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (1651113984 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (550371328 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-249387008 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-51597312 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (24336384 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (2924544 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-1418752 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-87040 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (43008 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1024 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-511 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_36 (n : ℕ) : ℤ :=
    (if 30 = n then (2147483648 : ℤ) else 0) +
    (if 31 = n then (-4294967296 : ℤ) else 0) +
    (if 32 = n then (-15032385536 : ℤ) else 0) +
    (if 33 = n then (34359738368 : ℤ) else 0) +
    (if 34 = n then (45097156608 : ℤ) else 0) +
    (if 35 = n then (-124554051584 : ℤ) else 0) +
    (if 36 = n then (-73014444032 : ℤ) else 0) +
    (if 37 = n then (270582939648 : ℤ) else 0) +
    (if 38 = n then (61001957376 : ℤ) else 0) +
    (if 39 = n then (-392586854400 : ℤ) else 0) +
    (if 40 = n then (-4362076160 : ℤ) else 0) +
    (if 41 = n then (401311006720 : ℤ) else 0) +
    (if 42 = n then (-52093255680 : ℤ) else 0) +
    (if 43 = n then (-297124495360 : ℤ) else 0) +
    (if 44 = n then (67914170368 : ℤ) else 0) +
    (if 45 = n then (161296154624 : ℤ) else 0) +
    (if 46 = n then (-48514859008 : ℤ) else 0) +
    (if 47 = n then (-64266436608 : ℤ) else 0) +
    (if 48 = n then (22819241984 : ℤ) else 0) +
    (if 49 = n then (18627952640 : ℤ) else 0) +
    (if 50 = n then (-7387676672 : ℤ) else 0) +
    (if 51 = n then (-3852599296 : ℤ) else 0) +
    (if 52 = n then (1651113984 : ℤ) else 0) +
    (if 53 = n then (550371328 : ℤ) else 0) +
    (if 54 = n then (-249387008 : ℤ) else 0) +
    (if 55 = n then (-51597312 : ℤ) else 0) +
    (if 56 = n then (24336384 : ℤ) else 0) +
    (if 57 = n then (2924544 : ℤ) else 0) +
    (if 58 = n then (-1418752 : ℤ) else 0) +
    (if 59 = n then (-87040 : ℤ) else 0) +
    (if 60 = n then (43008 : ℤ) else 0) +
    (if 61 = n then (1024 : ℤ) else 0) +
    (if 62 = n then (-511 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_36 (n : ℕ) :
    fixedRowPData_36.coeff n = fixedRowPCoeff_36 n := by
  simp only [fixedRowPData_36, fixedRowPCoeff_36, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_36 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_36 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_36, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_36 : ∀ k : Fin 63,
    fixedReversedTCoeff_32 (k.val + 2) - 2 * fixedReversedTCoeff_32 (k.val + 1) + fixedReversedTCoeff_32 k.val = fixedRowPCoeff_36 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_36 :
    (1 - X) ^ 2 * fixedReversedTData_32 = fixedRowPData_36 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_32, fixed_rowP_typed_coeff_36]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_32, fixed_rowP_typed_coeff_36]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_32, fixed_rowP_typed_coeff_36]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_36 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_32 _ (by omega),
              fixed_reversedT_typed_tail_32 _ (by omega), fixed_reversedT_typed_tail_32 _ hn',
              fixed_rowP_typed_tail_36 _ (by omega)]
            decide

theorem fixed_rowP_typed_36 : rowP 1 36 = fixedRowPData_36 := by
  calc
    rowP 1 36 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_32 :=
      fixedTyped_rowP_of_parameters 1 36 2 63 32 fixedChebyshevTData_32
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_32
    _ = fixedRowPData_36 := by
      rw [fixed_reversedT_typed_data_32, fixed_rowP_typed_factor_36]

def fixedRowDData_36 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 31 (2147483648 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-4294967296 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-13958643712 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (32212254720 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (38386270208 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-108984795136 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-55431921664 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (219848638464 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (37295751168 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-294440140800 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (9269411840 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (275901317120 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-45099253760 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-185702809600 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (47486861312 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (90729086976 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-29297934336 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-32133218304 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (11991744512 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (8149729280 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-3352502272 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-1444724736 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (636366848 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (171991040 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-79545856 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-12899328 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (6175488 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (548352 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-268736 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-10880 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (5408 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (64 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-32 : ℤ)

def fixedRowDCoeff_36 (n : ℕ) : ℤ :=
    (if 31 = n then (2147483648 : ℤ) else 0) +
    (if 32 = n then (-4294967296 : ℤ) else 0) +
    (if 33 = n then (-13958643712 : ℤ) else 0) +
    (if 34 = n then (32212254720 : ℤ) else 0) +
    (if 35 = n then (38386270208 : ℤ) else 0) +
    (if 36 = n then (-108984795136 : ℤ) else 0) +
    (if 37 = n then (-55431921664 : ℤ) else 0) +
    (if 38 = n then (219848638464 : ℤ) else 0) +
    (if 39 = n then (37295751168 : ℤ) else 0) +
    (if 40 = n then (-294440140800 : ℤ) else 0) +
    (if 41 = n then (9269411840 : ℤ) else 0) +
    (if 42 = n then (275901317120 : ℤ) else 0) +
    (if 43 = n then (-45099253760 : ℤ) else 0) +
    (if 44 = n then (-185702809600 : ℤ) else 0) +
    (if 45 = n then (47486861312 : ℤ) else 0) +
    (if 46 = n then (90729086976 : ℤ) else 0) +
    (if 47 = n then (-29297934336 : ℤ) else 0) +
    (if 48 = n then (-32133218304 : ℤ) else 0) +
    (if 49 = n then (11991744512 : ℤ) else 0) +
    (if 50 = n then (8149729280 : ℤ) else 0) +
    (if 51 = n then (-3352502272 : ℤ) else 0) +
    (if 52 = n then (-1444724736 : ℤ) else 0) +
    (if 53 = n then (636366848 : ℤ) else 0) +
    (if 54 = n then (171991040 : ℤ) else 0) +
    (if 55 = n then (-79545856 : ℤ) else 0) +
    (if 56 = n then (-12899328 : ℤ) else 0) +
    (if 57 = n then (6175488 : ℤ) else 0) +
    (if 58 = n then (548352 : ℤ) else 0) +
    (if 59 = n then (-268736 : ℤ) else 0) +
    (if 60 = n then (-10880 : ℤ) else 0) +
    (if 61 = n then (5408 : ℤ) else 0) +
    (if 62 = n then (64 : ℤ) else 0) +
    (if 63 = n then (-32 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_36 (n : ℕ) :
    fixedRowDData_36.coeff n = fixedRowDCoeff_36 n := by
  simp only [fixedRowDData_36, fixedRowDCoeff_36, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_36 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_36 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_36, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_36 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_31 (k.val + 2) - 2 * fixedReversedUCoeff_31 (k.val + 1) + fixedReversedUCoeff_31 k.val) = fixedRowDCoeff_36 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_36 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_31 = fixedRowDData_36 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_31, fixed_rowD_typed_coeff_36]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_31, fixed_rowD_typed_coeff_36]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_31, fixed_rowD_typed_coeff_36]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_36 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_31 _ (by omega),
              fixed_reversedU_typed_tail_31 _ (by omega), fixed_reversedU_typed_tail_31 _ hn',
              fixed_rowD_typed_tail_36 _ (by omega)]
            decide

theorem fixed_rowD_typed_36 : rowD 1 36 = fixedRowDData_36 := by
  calc
    rowD 1 36 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_31 :=
      fixedTyped_rowD_of_parameters 1 36 2 63 31 (1)
        fixedChebyshevUData_31 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_31
    _ = fixedRowDData_36 := by
      rw [fixed_reversedU_typed_data_31, fixed_rowD_typed_factor_36]

end InternalCatalan

end

end

end OAI
