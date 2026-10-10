import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT40To44
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU40To43

namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_48 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 18 (8796093022208 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (-17592186044416 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-87960930222080 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (193514046488576 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (399122720882688 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-991759488253952 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-1076421883592704 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (3144603255439360 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (1881848510676992 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-6908300276793344 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-2125630854397952 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (11159561985589248 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (1284817991761920 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-13729197969113088 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (291546675019776 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (13146104619073536 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-1609028429938688 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-9928047759196160 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (1985609551839232 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (5956828655517696 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-1554907479932928 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-2847013695651840 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (882338955264000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (1082335785123840 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-378394737377280 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-325546310369280 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (124402312151040 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (76741686067200 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-31381868052480 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-13977949962240 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (6024978432000 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (1927993098240 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-866090649600 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-195811799040 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (90866913280 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (14077972480 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-6700573440 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-676825600 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (328438528 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (19948544 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-9818424 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-311696 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (154880 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (1936 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (-967 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (1 : ℤ)

def fixedRowPCoeff_48 (n : ℕ) : ℤ :=
    (if 18 = n then (8796093022208 : ℤ) else 0) +
    (if 19 = n then (-17592186044416 : ℤ) else 0) +
    (if 20 = n then (-87960930222080 : ℤ) else 0) +
    (if 21 = n then (193514046488576 : ℤ) else 0) +
    (if 22 = n then (399122720882688 : ℤ) else 0) +
    (if 23 = n then (-991759488253952 : ℤ) else 0) +
    (if 24 = n then (-1076421883592704 : ℤ) else 0) +
    (if 25 = n then (3144603255439360 : ℤ) else 0) +
    (if 26 = n then (1881848510676992 : ℤ) else 0) +
    (if 27 = n then (-6908300276793344 : ℤ) else 0) +
    (if 28 = n then (-2125630854397952 : ℤ) else 0) +
    (if 29 = n then (11159561985589248 : ℤ) else 0) +
    (if 30 = n then (1284817991761920 : ℤ) else 0) +
    (if 31 = n then (-13729197969113088 : ℤ) else 0) +
    (if 32 = n then (291546675019776 : ℤ) else 0) +
    (if 33 = n then (13146104619073536 : ℤ) else 0) +
    (if 34 = n then (-1609028429938688 : ℤ) else 0) +
    (if 35 = n then (-9928047759196160 : ℤ) else 0) +
    (if 36 = n then (1985609551839232 : ℤ) else 0) +
    (if 37 = n then (5956828655517696 : ℤ) else 0) +
    (if 38 = n then (-1554907479932928 : ℤ) else 0) +
    (if 39 = n then (-2847013695651840 : ℤ) else 0) +
    (if 40 = n then (882338955264000 : ℤ) else 0) +
    (if 41 = n then (1082335785123840 : ℤ) else 0) +
    (if 42 = n then (-378394737377280 : ℤ) else 0) +
    (if 43 = n then (-325546310369280 : ℤ) else 0) +
    (if 44 = n then (124402312151040 : ℤ) else 0) +
    (if 45 = n then (76741686067200 : ℤ) else 0) +
    (if 46 = n then (-31381868052480 : ℤ) else 0) +
    (if 47 = n then (-13977949962240 : ℤ) else 0) +
    (if 48 = n then (6024978432000 : ℤ) else 0) +
    (if 49 = n then (1927993098240 : ℤ) else 0) +
    (if 50 = n then (-866090649600 : ℤ) else 0) +
    (if 51 = n then (-195811799040 : ℤ) else 0) +
    (if 52 = n then (90866913280 : ℤ) else 0) +
    (if 53 = n then (14077972480 : ℤ) else 0) +
    (if 54 = n then (-6700573440 : ℤ) else 0) +
    (if 55 = n then (-676825600 : ℤ) else 0) +
    (if 56 = n then (328438528 : ℤ) else 0) +
    (if 57 = n then (19948544 : ℤ) else 0) +
    (if 58 = n then (-9818424 : ℤ) else 0) +
    (if 59 = n then (-311696 : ℤ) else 0) +
    (if 60 = n then (154880 : ℤ) else 0) +
    (if 61 = n then (1936 : ℤ) else 0) +
    (if 62 = n then (-967 : ℤ) else 0) +
    (if 63 = n then (-2 : ℤ) else 0) +
    (if 64 = n then (1 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_48 (n : ℕ) :
    fixedRowPData_48.coeff n = fixedRowPCoeff_48 n := by
  simp only [fixedRowPData_48, fixedRowPCoeff_48, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_48 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_48 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_48, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_48 : ∀ k : Fin 63,
    fixedReversedTCoeff_44 (k.val + 2) - 2 * fixedReversedTCoeff_44 (k.val + 1) + fixedReversedTCoeff_44 k.val = fixedRowPCoeff_48 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_48 :
    (1 - X) ^ 2 * fixedReversedTData_44 = fixedRowPData_48 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_44, fixed_rowP_typed_coeff_48]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_44, fixed_rowP_typed_coeff_48]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_44, fixed_rowP_typed_coeff_48]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_48 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_44 _ (by omega),
              fixed_reversedT_typed_tail_44 _ (by omega), fixed_reversedT_typed_tail_44 _ hn',
              fixed_rowP_typed_tail_48 _ (by omega)]
            decide

theorem fixed_rowP_typed_48 : rowP 1 48 = fixedRowPData_48 := by
  calc
    rowP 1 48 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_44 :=
      fixedTyped_rowP_of_parameters 1 48 2 63 44 fixedChebyshevTData_44
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_44
    _ = fixedRowPData_48 := by
      rw [fixed_reversedT_typed_data_44, fixed_rowP_typed_factor_48]

def fixedRowDData_48 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 19 (8796093022208 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-17592186044416 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-83562883710976 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (184717953466368 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (358440790654976 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-901599534776320 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-907097092915200 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (2715793720606720 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (1468225980203008 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-5652245681012736 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-1485526108471296 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (8623297897955328 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (680786676154368 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-9984871250264064 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (510809050447872 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (8963253149368320 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-1322702287667200 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-6317848574033920 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (1398952184250368 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (3519944205533184 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-983513822134272 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-1552916561264640 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (505874334351360 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (541167892561920 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-196596148469760 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-147975595622400 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (58290634752000 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (31394326118400 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-13155717611520 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-5082890895360 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (2234719272960 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (613452349440 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-280024565760 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-53403217920 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (25101839360 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (3199539200 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-1538240000 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-123059200 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (60169472 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (2720256 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-1345960 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-28336 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (14124 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (88 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-44 : ℤ)

def fixedRowDCoeff_48 (n : ℕ) : ℤ :=
    (if 19 = n then (8796093022208 : ℤ) else 0) +
    (if 20 = n then (-17592186044416 : ℤ) else 0) +
    (if 21 = n then (-83562883710976 : ℤ) else 0) +
    (if 22 = n then (184717953466368 : ℤ) else 0) +
    (if 23 = n then (358440790654976 : ℤ) else 0) +
    (if 24 = n then (-901599534776320 : ℤ) else 0) +
    (if 25 = n then (-907097092915200 : ℤ) else 0) +
    (if 26 = n then (2715793720606720 : ℤ) else 0) +
    (if 27 = n then (1468225980203008 : ℤ) else 0) +
    (if 28 = n then (-5652245681012736 : ℤ) else 0) +
    (if 29 = n then (-1485526108471296 : ℤ) else 0) +
    (if 30 = n then (8623297897955328 : ℤ) else 0) +
    (if 31 = n then (680786676154368 : ℤ) else 0) +
    (if 32 = n then (-9984871250264064 : ℤ) else 0) +
    (if 33 = n then (510809050447872 : ℤ) else 0) +
    (if 34 = n then (8963253149368320 : ℤ) else 0) +
    (if 35 = n then (-1322702287667200 : ℤ) else 0) +
    (if 36 = n then (-6317848574033920 : ℤ) else 0) +
    (if 37 = n then (1398952184250368 : ℤ) else 0) +
    (if 38 = n then (3519944205533184 : ℤ) else 0) +
    (if 39 = n then (-983513822134272 : ℤ) else 0) +
    (if 40 = n then (-1552916561264640 : ℤ) else 0) +
    (if 41 = n then (505874334351360 : ℤ) else 0) +
    (if 42 = n then (541167892561920 : ℤ) else 0) +
    (if 43 = n then (-196596148469760 : ℤ) else 0) +
    (if 44 = n then (-147975595622400 : ℤ) else 0) +
    (if 45 = n then (58290634752000 : ℤ) else 0) +
    (if 46 = n then (31394326118400 : ℤ) else 0) +
    (if 47 = n then (-13155717611520 : ℤ) else 0) +
    (if 48 = n then (-5082890895360 : ℤ) else 0) +
    (if 49 = n then (2234719272960 : ℤ) else 0) +
    (if 50 = n then (613452349440 : ℤ) else 0) +
    (if 51 = n then (-280024565760 : ℤ) else 0) +
    (if 52 = n then (-53403217920 : ℤ) else 0) +
    (if 53 = n then (25101839360 : ℤ) else 0) +
    (if 54 = n then (3199539200 : ℤ) else 0) +
    (if 55 = n then (-1538240000 : ℤ) else 0) +
    (if 56 = n then (-123059200 : ℤ) else 0) +
    (if 57 = n then (60169472 : ℤ) else 0) +
    (if 58 = n then (2720256 : ℤ) else 0) +
    (if 59 = n then (-1345960 : ℤ) else 0) +
    (if 60 = n then (-28336 : ℤ) else 0) +
    (if 61 = n then (14124 : ℤ) else 0) +
    (if 62 = n then (88 : ℤ) else 0) +
    (if 63 = n then (-44 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_48 (n : ℕ) :
    fixedRowDData_48.coeff n = fixedRowDCoeff_48 n := by
  simp only [fixedRowDData_48, fixedRowDCoeff_48, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_48 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_48 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_48, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_48 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_43 (k.val + 2) - 2 * fixedReversedUCoeff_43 (k.val + 1) + fixedReversedUCoeff_43 k.val) = fixedRowDCoeff_48 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_48 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_43 = fixedRowDData_48 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_43, fixed_rowD_typed_coeff_48]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_43, fixed_rowD_typed_coeff_48]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_43, fixed_rowD_typed_coeff_48]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_48 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_43 _ (by omega),
              fixed_reversedU_typed_tail_43 _ (by omega), fixed_reversedU_typed_tail_43 _ hn',
              fixed_rowD_typed_tail_48 _ (by omega)]
            decide

theorem fixed_rowD_typed_48 : rowD 1 48 = fixedRowDData_48 := by
  calc
    rowD 1 48 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_43 :=
      fixedTyped_rowD_of_parameters 1 48 2 63 43 (1)
        fixedChebyshevUData_43 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_43
    _ = fixedRowDData_48 := by
      rw [fixed_reversedU_typed_data_43, fixed_rowD_typed_factor_48]

end InternalCatalan

end

end OAI
