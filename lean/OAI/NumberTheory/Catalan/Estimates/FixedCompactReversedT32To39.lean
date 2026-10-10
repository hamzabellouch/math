import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedTData_32 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-512 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (43520 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-1462272 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (25798656 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-275185664 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (1926299648 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-9313976320 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (32133218304 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-80648077312 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (148562247680 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-200655503360 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (196293427200 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-135291469824 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (62277025792 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-17179869184 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (2147483648 : ℤ)

def fixedReversedTCoeff_32 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-512 : ℤ) else 0) +
    (if 58 = n then (43520 : ℤ) else 0) +
    (if 56 = n then (-1462272 : ℤ) else 0) +
    (if 54 = n then (25798656 : ℤ) else 0) +
    (if 52 = n then (-275185664 : ℤ) else 0) +
    (if 50 = n then (1926299648 : ℤ) else 0) +
    (if 48 = n then (-9313976320 : ℤ) else 0) +
    (if 46 = n then (32133218304 : ℤ) else 0) +
    (if 44 = n then (-80648077312 : ℤ) else 0) +
    (if 42 = n then (148562247680 : ℤ) else 0) +
    (if 40 = n then (-200655503360 : ℤ) else 0) +
    (if 38 = n then (196293427200 : ℤ) else 0) +
    (if 36 = n then (-135291469824 : ℤ) else 0) +
    (if 34 = n then (62277025792 : ℤ) else 0) +
    (if 32 = n then (-17179869184 : ℤ) else 0) +
    (if 30 = n then (2147483648 : ℤ) else 0)

theorem fixed_reversedT_typed_data_32 : reversedRow 63 fixedChebyshevTData_32 = fixedReversedTData_32 := by
  simp only [fixedChebyshevTData_32, fixedReversedTData_32, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-512 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (43520 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-1462272 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (25798656 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-275185664 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (1926299648 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-9313976320 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (32133218304 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-80648077312 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (148562247680 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-200655503360 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (196293427200 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-135291469824 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (62277025792 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (-17179869184 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (2147483648 : ℤ) 32 (by decide)]

theorem fixed_reversedT_typed_coeff_32 (n : ℕ) :
    fixedReversedTData_32.coeff n = fixedReversedTCoeff_32 n := by
  simp only [fixedReversedTData_32, fixedReversedTCoeff_32, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_32 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_32 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_32, ite_eq_right, add_zero]

def fixedReversedTData_33 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (33 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-5984 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (323136 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-8186112 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (118243840 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-1083543552 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (6723526656 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-29455450112 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (93564370944 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-218864025600 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (379364311040 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-485826232320 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (453437816832 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-299708186624 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (132875550720 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-35433480192 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (4294967296 : ℤ)

def fixedReversedTCoeff_33 (n : ℕ) : ℤ :=
    (if 61 = n then (33 : ℤ) else 0) +
    (if 59 = n then (-5984 : ℤ) else 0) +
    (if 57 = n then (323136 : ℤ) else 0) +
    (if 55 = n then (-8186112 : ℤ) else 0) +
    (if 53 = n then (118243840 : ℤ) else 0) +
    (if 51 = n then (-1083543552 : ℤ) else 0) +
    (if 49 = n then (6723526656 : ℤ) else 0) +
    (if 47 = n then (-29455450112 : ℤ) else 0) +
    (if 45 = n then (93564370944 : ℤ) else 0) +
    (if 43 = n then (-218864025600 : ℤ) else 0) +
    (if 41 = n then (379364311040 : ℤ) else 0) +
    (if 39 = n then (-485826232320 : ℤ) else 0) +
    (if 37 = n then (453437816832 : ℤ) else 0) +
    (if 35 = n then (-299708186624 : ℤ) else 0) +
    (if 33 = n then (132875550720 : ℤ) else 0) +
    (if 31 = n then (-35433480192 : ℤ) else 0) +
    (if 29 = n then (4294967296 : ℤ) else 0)

theorem fixed_reversedT_typed_data_33 : reversedRow 63 fixedChebyshevTData_33 = fixedReversedTData_33 := by
  simp only [fixedChebyshevTData_33, fixedReversedTData_33, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (33 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-5984 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (323136 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-8186112 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (118243840 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-1083543552 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (6723526656 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-29455450112 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (93564370944 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-218864025600 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (379364311040 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-485826232320 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (453437816832 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (-299708186624 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (132875550720 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (-35433480192 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (4294967296 : ℤ) 33 (by decide)]

theorem fixed_reversedT_typed_coeff_33 (n : ℕ) :
    fixedReversedTData_33.coeff n = fixedReversedTCoeff_33 n := by
  simp only [fixedReversedTData_33, fixedReversedTCoeff_33, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_33 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_33 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_33, ite_eq_right, add_zero]

def fixedReversedTData_34 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (578 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-55488 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (2108544 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-42170880 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (511673344 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-4093386752 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (22761029632 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-91044118528 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (267776819200 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-586290298880 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (959384125440 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-1167945891840 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (1042167103488 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-661693399040 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (282930970624 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-73014444032 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (8589934592 : ℤ)

def fixedReversedTCoeff_34 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (578 : ℤ) else 0) +
    (if 58 = n then (-55488 : ℤ) else 0) +
    (if 56 = n then (2108544 : ℤ) else 0) +
    (if 54 = n then (-42170880 : ℤ) else 0) +
    (if 52 = n then (511673344 : ℤ) else 0) +
    (if 50 = n then (-4093386752 : ℤ) else 0) +
    (if 48 = n then (22761029632 : ℤ) else 0) +
    (if 46 = n then (-91044118528 : ℤ) else 0) +
    (if 44 = n then (267776819200 : ℤ) else 0) +
    (if 42 = n then (-586290298880 : ℤ) else 0) +
    (if 40 = n then (959384125440 : ℤ) else 0) +
    (if 38 = n then (-1167945891840 : ℤ) else 0) +
    (if 36 = n then (1042167103488 : ℤ) else 0) +
    (if 34 = n then (-661693399040 : ℤ) else 0) +
    (if 32 = n then (282930970624 : ℤ) else 0) +
    (if 30 = n then (-73014444032 : ℤ) else 0) +
    (if 28 = n then (8589934592 : ℤ) else 0)

theorem fixed_reversedT_typed_data_34 : reversedRow 63 fixedChebyshevTData_34 = fixedReversedTData_34 := by
  simp only [fixedChebyshevTData_34, fixedReversedTData_34, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (578 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-55488 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (2108544 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-42170880 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (511673344 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-4093386752 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (22761029632 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-91044118528 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (267776819200 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-586290298880 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (959384125440 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-1167945891840 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (1042167103488 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (-661693399040 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (282930970624 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (-73014444032 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (8589934592 : ℤ) 34 (by decide)]

theorem fixed_reversedT_typed_coeff_34 (n : ℕ) :
    fixedReversedTData_34.coeff n = fixedReversedTCoeff_34 n := by
  simp only [fixedReversedTData_34, fixedReversedTCoeff_34, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_34 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_34 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_34, ite_eq_right, add_zero]

def fixedReversedTData_35 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-35 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (7140 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-434112 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (12403200 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-202585600 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (2106890240 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-14910300160 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (74977509376 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-275652608000 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (754417664000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-1551944908800 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (2404594483200 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-2789329600512 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (2384042393600 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-1456262348800 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (601295421440 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-150323855360 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (17179869184 : ℤ)

def fixedReversedTCoeff_35 (n : ℕ) : ℤ :=
    (if 61 = n then (-35 : ℤ) else 0) +
    (if 59 = n then (7140 : ℤ) else 0) +
    (if 57 = n then (-434112 : ℤ) else 0) +
    (if 55 = n then (12403200 : ℤ) else 0) +
    (if 53 = n then (-202585600 : ℤ) else 0) +
    (if 51 = n then (2106890240 : ℤ) else 0) +
    (if 49 = n then (-14910300160 : ℤ) else 0) +
    (if 47 = n then (74977509376 : ℤ) else 0) +
    (if 45 = n then (-275652608000 : ℤ) else 0) +
    (if 43 = n then (754417664000 : ℤ) else 0) +
    (if 41 = n then (-1551944908800 : ℤ) else 0) +
    (if 39 = n then (2404594483200 : ℤ) else 0) +
    (if 37 = n then (-2789329600512 : ℤ) else 0) +
    (if 35 = n then (2384042393600 : ℤ) else 0) +
    (if 33 = n then (-1456262348800 : ℤ) else 0) +
    (if 31 = n then (601295421440 : ℤ) else 0) +
    (if 29 = n then (-150323855360 : ℤ) else 0) +
    (if 27 = n then (17179869184 : ℤ) else 0)

theorem fixed_reversedT_typed_data_35 : reversedRow 63 fixedChebyshevTData_35 = fixedReversedTData_35 := by
  simp only [fixedChebyshevTData_35, fixedReversedTData_35, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-35 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (7140 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-434112 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (12403200 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-202585600 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (2106890240 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-14910300160 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (74977509376 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-275652608000 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (754417664000 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-1551944908800 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (2404594483200 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-2789329600512 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (2384042393600 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (-1456262348800 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (601295421440 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (-150323855360 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (17179869184 : ℤ) 35 (by decide)]

theorem fixed_reversedT_typed_coeff_35 (n : ℕ) :
    fixedReversedTData_35.coeff n = fixedReversedTCoeff_35 n := by
  simp only [fixedReversedTData_35, fixedReversedTCoeff_35, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_35 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_35 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_35, ite_eq_right, add_zero]

def fixedReversedTData_36 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-648 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (69768 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-2976768 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (66977280 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-916844544 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (8307167232 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-52581629952 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (240999137280 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-819082035200 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (2095125626880 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-4063273943040 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (5977134858240 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-6620826304512 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (5429778186240 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-3195455668224 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (1275605286912 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-309237645312 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (34359738368 : ℤ)

def fixedReversedTCoeff_36 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-648 : ℤ) else 0) +
    (if 58 = n then (69768 : ℤ) else 0) +
    (if 56 = n then (-2976768 : ℤ) else 0) +
    (if 54 = n then (66977280 : ℤ) else 0) +
    (if 52 = n then (-916844544 : ℤ) else 0) +
    (if 50 = n then (8307167232 : ℤ) else 0) +
    (if 48 = n then (-52581629952 : ℤ) else 0) +
    (if 46 = n then (240999137280 : ℤ) else 0) +
    (if 44 = n then (-819082035200 : ℤ) else 0) +
    (if 42 = n then (2095125626880 : ℤ) else 0) +
    (if 40 = n then (-4063273943040 : ℤ) else 0) +
    (if 38 = n then (5977134858240 : ℤ) else 0) +
    (if 36 = n then (-6620826304512 : ℤ) else 0) +
    (if 34 = n then (5429778186240 : ℤ) else 0) +
    (if 32 = n then (-3195455668224 : ℤ) else 0) +
    (if 30 = n then (1275605286912 : ℤ) else 0) +
    (if 28 = n then (-309237645312 : ℤ) else 0) +
    (if 26 = n then (34359738368 : ℤ) else 0)

theorem fixed_reversedT_typed_data_36 : reversedRow 63 fixedChebyshevTData_36 = fixedReversedTData_36 := by
  simp only [fixedChebyshevTData_36, fixedReversedTData_36, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-648 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (69768 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-2976768 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (66977280 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-916844544 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (8307167232 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-52581629952 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (240999137280 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-819082035200 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (2095125626880 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-4063273943040 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (5977134858240 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-6620826304512 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (5429778186240 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (-3195455668224 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (1275605286912 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (-309237645312 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (34359738368 : ℤ) 36 (by decide)]

theorem fixed_reversedT_typed_coeff_36 (n : ℕ) :
    fixedReversedTData_36.coeff n = fixedReversedTCoeff_36 n := by
  simp only [fixedReversedTData_36, fixedReversedTCoeff_36, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_36 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_36 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_36, ite_eq_right, add_zero]

def fixedReversedTData_37 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (37 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-8436 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (573648 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-18356736 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (336540160 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-3940579328 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (31524634624 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-180140769280 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (757650882560 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-2392581734400 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (5742196162560 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-10531142369280 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (14743599316992 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-15625695002624 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (12315818721280 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-6992206757888 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (2701534429184 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-635655159808 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (68719476736 : ℤ)

def fixedReversedTCoeff_37 (n : ℕ) : ℤ :=
    (if 61 = n then (37 : ℤ) else 0) +
    (if 59 = n then (-8436 : ℤ) else 0) +
    (if 57 = n then (573648 : ℤ) else 0) +
    (if 55 = n then (-18356736 : ℤ) else 0) +
    (if 53 = n then (336540160 : ℤ) else 0) +
    (if 51 = n then (-3940579328 : ℤ) else 0) +
    (if 49 = n then (31524634624 : ℤ) else 0) +
    (if 47 = n then (-180140769280 : ℤ) else 0) +
    (if 45 = n then (757650882560 : ℤ) else 0) +
    (if 43 = n then (-2392581734400 : ℤ) else 0) +
    (if 41 = n then (5742196162560 : ℤ) else 0) +
    (if 39 = n then (-10531142369280 : ℤ) else 0) +
    (if 37 = n then (14743599316992 : ℤ) else 0) +
    (if 35 = n then (-15625695002624 : ℤ) else 0) +
    (if 33 = n then (12315818721280 : ℤ) else 0) +
    (if 31 = n then (-6992206757888 : ℤ) else 0) +
    (if 29 = n then (2701534429184 : ℤ) else 0) +
    (if 27 = n then (-635655159808 : ℤ) else 0) +
    (if 25 = n then (68719476736 : ℤ) else 0)

theorem fixed_reversedT_typed_data_37 : reversedRow 63 fixedChebyshevTData_37 = fixedReversedTData_37 := by
  simp only [fixedChebyshevTData_37, fixedReversedTData_37, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (37 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-8436 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (573648 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-18356736 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (336540160 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-3940579328 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (31524634624 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-180140769280 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (757650882560 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-2392581734400 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (5742196162560 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-10531142369280 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (14743599316992 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (-15625695002624 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (12315818721280 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (-6992206757888 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (2701534429184 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (-635655159808 : ℤ) 35 (by decide),
    fixedTyped_reversedRow_monomial (68719476736 : ℤ) 37 (by decide)]

theorem fixed_reversedT_typed_coeff_37 (n : ℕ) :
    fixedReversedTData_37.coeff n = fixedReversedTCoeff_37 n := by
  simp only [fixedReversedTData_37, fixedReversedTCoeff_37, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_37 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_37 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_37, ite_eq_right, add_zero]

def fixedReversedTData_38 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (722 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-86640 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (4124064 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-103690752 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (1589924864 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-16188325888 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (115630899200 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-601280675840 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (2334383800320 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-6880289095680 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (15547666268160 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-27039419596800 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (36108024938496 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-36681168191488 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (27827093110784 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-15260018802688 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (5712306503680 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-1305670057984 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (137438953472 : ℤ)

def fixedReversedTCoeff_38 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (722 : ℤ) else 0) +
    (if 58 = n then (-86640 : ℤ) else 0) +
    (if 56 = n then (4124064 : ℤ) else 0) +
    (if 54 = n then (-103690752 : ℤ) else 0) +
    (if 52 = n then (1589924864 : ℤ) else 0) +
    (if 50 = n then (-16188325888 : ℤ) else 0) +
    (if 48 = n then (115630899200 : ℤ) else 0) +
    (if 46 = n then (-601280675840 : ℤ) else 0) +
    (if 44 = n then (2334383800320 : ℤ) else 0) +
    (if 42 = n then (-6880289095680 : ℤ) else 0) +
    (if 40 = n then (15547666268160 : ℤ) else 0) +
    (if 38 = n then (-27039419596800 : ℤ) else 0) +
    (if 36 = n then (36108024938496 : ℤ) else 0) +
    (if 34 = n then (-36681168191488 : ℤ) else 0) +
    (if 32 = n then (27827093110784 : ℤ) else 0) +
    (if 30 = n then (-15260018802688 : ℤ) else 0) +
    (if 28 = n then (5712306503680 : ℤ) else 0) +
    (if 26 = n then (-1305670057984 : ℤ) else 0) +
    (if 24 = n then (137438953472 : ℤ) else 0)

theorem fixed_reversedT_typed_data_38 : reversedRow 63 fixedChebyshevTData_38 = fixedReversedTData_38 := by
  simp only [fixedChebyshevTData_38, fixedReversedTData_38, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (722 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-86640 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (4124064 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-103690752 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (1589924864 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-16188325888 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (115630899200 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-601280675840 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (2334383800320 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-6880289095680 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (15547666268160 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-27039419596800 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (36108024938496 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (-36681168191488 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (27827093110784 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (-15260018802688 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (5712306503680 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (-1305670057984 : ℤ) 36 (by decide),
    fixedTyped_reversedRow_monomial (137438953472 : ℤ) 38 (by decide)]

theorem fixed_reversedT_typed_coeff_38 (n : ℕ) :
    fixedReversedTData_38.coeff n = fixedReversedTCoeff_38 n := by
  simp only [fixedReversedTData_38, fixedReversedTCoeff_38, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_38 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_38 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_38, ite_eq_right, add_zero]

def fixedReversedTData_39 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-39 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (9880 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-746928 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (26604864 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-543921664 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (7120429056 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-63901286400 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (411402567680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-1960212234240 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (7061349335040 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-19502774353920 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (41626474905600 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-68822438510592 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (87841744879616 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-85678155104256 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (62646392979456 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-33221572034560 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (12060268167168 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-2680059592704 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (274877906944 : ℤ)

def fixedReversedTCoeff_39 (n : ℕ) : ℤ :=
    (if 61 = n then (-39 : ℤ) else 0) +
    (if 59 = n then (9880 : ℤ) else 0) +
    (if 57 = n then (-746928 : ℤ) else 0) +
    (if 55 = n then (26604864 : ℤ) else 0) +
    (if 53 = n then (-543921664 : ℤ) else 0) +
    (if 51 = n then (7120429056 : ℤ) else 0) +
    (if 49 = n then (-63901286400 : ℤ) else 0) +
    (if 47 = n then (411402567680 : ℤ) else 0) +
    (if 45 = n then (-1960212234240 : ℤ) else 0) +
    (if 43 = n then (7061349335040 : ℤ) else 0) +
    (if 41 = n then (-19502774353920 : ℤ) else 0) +
    (if 39 = n then (41626474905600 : ℤ) else 0) +
    (if 37 = n then (-68822438510592 : ℤ) else 0) +
    (if 35 = n then (87841744879616 : ℤ) else 0) +
    (if 33 = n then (-85678155104256 : ℤ) else 0) +
    (if 31 = n then (62646392979456 : ℤ) else 0) +
    (if 29 = n then (-33221572034560 : ℤ) else 0) +
    (if 27 = n then (12060268167168 : ℤ) else 0) +
    (if 25 = n then (-2680059592704 : ℤ) else 0) +
    (if 23 = n then (274877906944 : ℤ) else 0)

theorem fixed_reversedT_typed_data_39 : reversedRow 63 fixedChebyshevTData_39 = fixedReversedTData_39 := by
  simp only [fixedChebyshevTData_39, fixedReversedTData_39, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-39 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (9880 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-746928 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (26604864 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-543921664 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (7120429056 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-63901286400 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (411402567680 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-1960212234240 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (7061349335040 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-19502774353920 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (41626474905600 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-68822438510592 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (87841744879616 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (-85678155104256 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (62646392979456 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (-33221572034560 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (12060268167168 : ℤ) 35 (by decide),
    fixedTyped_reversedRow_monomial (-2680059592704 : ℤ) 37 (by decide),
    fixedTyped_reversedRow_monomial (274877906944 : ℤ) 39 (by decide)]

theorem fixed_reversedT_typed_coeff_39 (n : ℕ) :
    fixedReversedTData_39.coeff n = fixedReversedTCoeff_39 n := by
  simp only [fixedReversedTData_39, fixedReversedTCoeff_39, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_39 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_39 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_39, ite_eq_right, add_zero]

end InternalCatalan

end

end

end OAI
