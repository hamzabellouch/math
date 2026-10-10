import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT40To44
import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedU40To43

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedRowPData_47 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 19 (4398046511104 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-8796093022208 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-42880953483264 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (94557999988736 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (189115999977472 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-472789999943680 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-493474562441216 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (1459739124826112 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (828121234276352 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-3115981593378816 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-881494792863744 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (4878971179106304 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (461524300726272 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-5802019780558848 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (224482908176384 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (5353053964206080 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-736044920078336 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-3880964124049408 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (827558526451712 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (2225847071145984 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-607049201221632 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-1011748668702720 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (324075745443840 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (363597177815040 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-130484471070720 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-102628235673600 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (40064484311040 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (22499267051520 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-9365458452480 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-3768350146560 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (1648653189120 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (471043768320 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-214259491840 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-42524784640 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (19939505920 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (2645772800 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-1269970944 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-105830912 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (51697008 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (2436896 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-1205204 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-26488 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (13201 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (86 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (-43 : ℤ)

def fixedRowPCoeff_47 (n : ℕ) : ℤ :=
    (if 19 = n then (4398046511104 : ℤ) else 0) +
    (if 20 = n then (-8796093022208 : ℤ) else 0) +
    (if 21 = n then (-42880953483264 : ℤ) else 0) +
    (if 22 = n then (94557999988736 : ℤ) else 0) +
    (if 23 = n then (189115999977472 : ℤ) else 0) +
    (if 24 = n then (-472789999943680 : ℤ) else 0) +
    (if 25 = n then (-493474562441216 : ℤ) else 0) +
    (if 26 = n then (1459739124826112 : ℤ) else 0) +
    (if 27 = n then (828121234276352 : ℤ) else 0) +
    (if 28 = n then (-3115981593378816 : ℤ) else 0) +
    (if 29 = n then (-881494792863744 : ℤ) else 0) +
    (if 30 = n then (4878971179106304 : ℤ) else 0) +
    (if 31 = n then (461524300726272 : ℤ) else 0) +
    (if 32 = n then (-5802019780558848 : ℤ) else 0) +
    (if 33 = n then (224482908176384 : ℤ) else 0) +
    (if 34 = n then (5353053964206080 : ℤ) else 0) +
    (if 35 = n then (-736044920078336 : ℤ) else 0) +
    (if 36 = n then (-3880964124049408 : ℤ) else 0) +
    (if 37 = n then (827558526451712 : ℤ) else 0) +
    (if 38 = n then (2225847071145984 : ℤ) else 0) +
    (if 39 = n then (-607049201221632 : ℤ) else 0) +
    (if 40 = n then (-1011748668702720 : ℤ) else 0) +
    (if 41 = n then (324075745443840 : ℤ) else 0) +
    (if 42 = n then (363597177815040 : ℤ) else 0) +
    (if 43 = n then (-130484471070720 : ℤ) else 0) +
    (if 44 = n then (-102628235673600 : ℤ) else 0) +
    (if 45 = n then (40064484311040 : ℤ) else 0) +
    (if 46 = n then (22499267051520 : ℤ) else 0) +
    (if 47 = n then (-9365458452480 : ℤ) else 0) +
    (if 48 = n then (-3768350146560 : ℤ) else 0) +
    (if 49 = n then (1648653189120 : ℤ) else 0) +
    (if 50 = n then (471043768320 : ℤ) else 0) +
    (if 51 = n then (-214259491840 : ℤ) else 0) +
    (if 52 = n then (-42524784640 : ℤ) else 0) +
    (if 53 = n then (19939505920 : ℤ) else 0) +
    (if 54 = n then (2645772800 : ℤ) else 0) +
    (if 55 = n then (-1269970944 : ℤ) else 0) +
    (if 56 = n then (-105830912 : ℤ) else 0) +
    (if 57 = n then (51697008 : ℤ) else 0) +
    (if 58 = n then (2436896 : ℤ) else 0) +
    (if 59 = n then (-1205204 : ℤ) else 0) +
    (if 60 = n then (-26488 : ℤ) else 0) +
    (if 61 = n then (13201 : ℤ) else 0) +
    (if 62 = n then (86 : ℤ) else 0) +
    (if 63 = n then (-43 : ℤ) else 0)

theorem fixed_rowP_typed_coeff_47 (n : ℕ) :
    fixedRowPData_47.coeff n = fixedRowPCoeff_47 n := by
  simp only [fixedRowPData_47, fixedRowPCoeff_47, coeff_add, coeff_monomial]

theorem fixed_rowP_typed_tail_47 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowPCoeff_47 n = 0 := by
  simp (disch := omega) only [fixedRowPCoeff_47, ite_eq_right, add_zero]

theorem fixed_rowP_typed_scalar_47 : ∀ k : Fin 63,
    fixedReversedTCoeff_43 (k.val + 2) - 2 * fixedReversedTCoeff_43 (k.val + 1) + fixedReversedTCoeff_43 k.val = fixedRowPCoeff_47 (k.val + 2) := by
  decide

theorem fixed_rowP_typed_factor_47 :
    (1 - X) ^ 2 * fixedReversedTData_43 = fixedRowPData_47 := by
  rw [fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_43, fixed_rowP_typed_coeff_47]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedT_typed_coeff_43, fixed_rowP_typed_coeff_47]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_X_mul,
            fixed_reversedT_typed_coeff_43, fixed_rowP_typed_coeff_47]
          by_cases hn : n < 63
          · exact fixed_rowP_typed_scalar_47 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedT_typed_tail_43 _ (by omega),
              fixed_reversedT_typed_tail_43 _ (by omega), fixed_reversedT_typed_tail_43 _ hn',
              fixed_rowP_typed_tail_47 _ (by omega)]
            decide

theorem fixed_rowP_typed_47 : rowP 1 47 = fixedRowPData_47 := by
  calc
    rowP 1 47 = (1 - X) ^ 2 * reversedRow 63 fixedChebyshevTData_43 :=
      fixedTyped_rowP_of_parameters 1 47 2 63 43 fixedChebyshevTData_43
        (by decide) (by decide) (by decide) fixed_chebyshevT_typed_43
    _ = fixedRowPData_47 := by
      rw [fixed_reversedT_typed_data_43, fixed_rowP_typed_factor_47]

def fixedRowDData_47 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 20 (4398046511104 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-8796093022208 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-40681930227712 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (90159953477632 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (169324790677504 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-428809534832640 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-413622530473984 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (1256054595780608 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (640104745926656 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-2536264087633920 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-604031315607552 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (3744326718849024 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (219262375428096 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-4182851469705216 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (286326142271488 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (3610199185162240 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-586657367588864 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-2436884449984512 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (571393657798656 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (1294097134387200 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-376464620912640 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-541167892561920 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (181798588907520 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (177570714746880 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-66111677399040 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-45347359948800 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (18226150440960 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (8895059066880 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-3790259159040 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-1314540748800 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (586066083840 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (142408581120 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-65765073920 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-10878433280 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (5162333440 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (553766400 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-268269056 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-17228288 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (8472464 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (283360 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-140756 : ℤ) +
    Polynomial.monomial (R := ℤ) 61 (-1848 : ℤ) +
    Polynomial.monomial (R := ℤ) 62 (923 : ℤ) +
    Polynomial.monomial (R := ℤ) 63 (2 : ℤ) +
    Polynomial.monomial (R := ℤ) 64 (-1 : ℤ)

def fixedRowDCoeff_47 (n : ℕ) : ℤ :=
    (if 20 = n then (4398046511104 : ℤ) else 0) +
    (if 21 = n then (-8796093022208 : ℤ) else 0) +
    (if 22 = n then (-40681930227712 : ℤ) else 0) +
    (if 23 = n then (90159953477632 : ℤ) else 0) +
    (if 24 = n then (169324790677504 : ℤ) else 0) +
    (if 25 = n then (-428809534832640 : ℤ) else 0) +
    (if 26 = n then (-413622530473984 : ℤ) else 0) +
    (if 27 = n then (1256054595780608 : ℤ) else 0) +
    (if 28 = n then (640104745926656 : ℤ) else 0) +
    (if 29 = n then (-2536264087633920 : ℤ) else 0) +
    (if 30 = n then (-604031315607552 : ℤ) else 0) +
    (if 31 = n then (3744326718849024 : ℤ) else 0) +
    (if 32 = n then (219262375428096 : ℤ) else 0) +
    (if 33 = n then (-4182851469705216 : ℤ) else 0) +
    (if 34 = n then (286326142271488 : ℤ) else 0) +
    (if 35 = n then (3610199185162240 : ℤ) else 0) +
    (if 36 = n then (-586657367588864 : ℤ) else 0) +
    (if 37 = n then (-2436884449984512 : ℤ) else 0) +
    (if 38 = n then (571393657798656 : ℤ) else 0) +
    (if 39 = n then (1294097134387200 : ℤ) else 0) +
    (if 40 = n then (-376464620912640 : ℤ) else 0) +
    (if 41 = n then (-541167892561920 : ℤ) else 0) +
    (if 42 = n then (181798588907520 : ℤ) else 0) +
    (if 43 = n then (177570714746880 : ℤ) else 0) +
    (if 44 = n then (-66111677399040 : ℤ) else 0) +
    (if 45 = n then (-45347359948800 : ℤ) else 0) +
    (if 46 = n then (18226150440960 : ℤ) else 0) +
    (if 47 = n then (8895059066880 : ℤ) else 0) +
    (if 48 = n then (-3790259159040 : ℤ) else 0) +
    (if 49 = n then (-1314540748800 : ℤ) else 0) +
    (if 50 = n then (586066083840 : ℤ) else 0) +
    (if 51 = n then (142408581120 : ℤ) else 0) +
    (if 52 = n then (-65765073920 : ℤ) else 0) +
    (if 53 = n then (-10878433280 : ℤ) else 0) +
    (if 54 = n then (5162333440 : ℤ) else 0) +
    (if 55 = n then (553766400 : ℤ) else 0) +
    (if 56 = n then (-268269056 : ℤ) else 0) +
    (if 57 = n then (-17228288 : ℤ) else 0) +
    (if 58 = n then (8472464 : ℤ) else 0) +
    (if 59 = n then (283360 : ℤ) else 0) +
    (if 60 = n then (-140756 : ℤ) else 0) +
    (if 61 = n then (-1848 : ℤ) else 0) +
    (if 62 = n then (923 : ℤ) else 0) +
    (if 63 = n then (2 : ℤ) else 0) +
    (if 64 = n then (-1 : ℤ) else 0)

theorem fixed_rowD_typed_coeff_47 (n : ℕ) :
    fixedRowDData_47.coeff n = fixedRowDCoeff_47 n := by
  simp only [fixedRowDData_47, fixedRowDCoeff_47, coeff_add, coeff_monomial]

theorem fixed_rowD_typed_tail_47 (n : ℕ) (hn : 65 ≤ n) :
    fixedRowDCoeff_47 n = 0 := by
  simp (disch := omega) only [fixedRowDCoeff_47, ite_eq_right, add_zero]

theorem fixed_rowD_typed_scalar_47 : ∀ k : Fin 63,
    (1 : ℤ) * (fixedReversedUCoeff_42 (k.val + 2) - 2 * fixedReversedUCoeff_42 (k.val + 1) + fixedReversedUCoeff_42 k.val) = fixedRowDCoeff_47 (k.val + 2) := by
  decide

theorem fixed_rowD_typed_factor_47 :
    Polynomial.C (1 : ℤ) * (1 - X) ^ 2 * fixedReversedUData_42 = fixedRowDData_47 := by
  rw [mul_assoc, fixedTyped_rowFactor]
  ext n
  cases n with
  | zero =>
      simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_42, fixed_rowD_typed_coeff_47]
      decide
  | succ n =>
      cases n with
      | zero =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            coeff_X_mul_zero, fixed_reversedU_typed_coeff_42, fixed_rowD_typed_coeff_47]
          decide
      | succ n =>
          simp only [coeff_add, coeff_sub, coeff_ofNat_mul, coeff_C_mul, coeff_X_mul,
            fixed_reversedU_typed_coeff_42, fixed_rowD_typed_coeff_47]
          by_cases hn : n < 63
          · exact fixed_rowD_typed_scalar_47 ⟨n, hn⟩
          · have hn' : 63 ≤ n := Nat.le_of_not_gt hn
            rw [fixed_reversedU_typed_tail_42 _ (by omega),
              fixed_reversedU_typed_tail_42 _ (by omega), fixed_reversedU_typed_tail_42 _ hn',
              fixed_rowD_typed_tail_47 _ (by omega)]
            decide

theorem fixed_rowD_typed_47 : rowD 1 47 = fixedRowDData_47 := by
  calc
    rowD 1 47 = Polynomial.C (1 : ℤ) * (1 - X) ^ 2 *
        reversedRow 63 fixedChebyshevUData_42 :=
      fixedTyped_rowD_of_parameters 1 47 2 63 42 (1)
        fixedChebyshevUData_42 (by decide) (by decide)
        (by decide) (by decide) fixed_chebyshevU_typed_42
    _ = fixedRowDData_47 := by
      rw [fixed_reversedU_typed_data_42, fixed_rowD_typed_factor_47]

end InternalCatalan

end

end

end OAI
