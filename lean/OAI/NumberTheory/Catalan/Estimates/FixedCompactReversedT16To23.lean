import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedTData_16 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-128 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (2688 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-21504 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (84480 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-180224 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (212992 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-131072 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (32768 : ℤ)

def fixedReversedTCoeff_16 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-128 : ℤ) else 0) +
    (if 58 = n then (2688 : ℤ) else 0) +
    (if 56 = n then (-21504 : ℤ) else 0) +
    (if 54 = n then (84480 : ℤ) else 0) +
    (if 52 = n then (-180224 : ℤ) else 0) +
    (if 50 = n then (212992 : ℤ) else 0) +
    (if 48 = n then (-131072 : ℤ) else 0) +
    (if 46 = n then (32768 : ℤ) else 0)

theorem fixed_reversedT_typed_data_16 : reversedRow 63 fixedChebyshevTData_16 = fixedReversedTData_16 := by
  simp only [fixedChebyshevTData_16, fixedReversedTData_16, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-128 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (2688 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-21504 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (84480 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-180224 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (212992 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-131072 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (32768 : ℤ) 16 (by decide)]

theorem fixed_reversedT_typed_coeff_16 (n : ℕ) :
    fixedReversedTData_16.coeff n = fixedReversedTCoeff_16 n := by
  simp only [fixedReversedTData_16, fixedReversedTCoeff_16, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_16 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_16 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_16, ite_eq_right, add_zero]

def fixedReversedTData_17 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (17 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-816 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (11424 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-71808 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (239360 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-452608 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (487424 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-278528 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (65536 : ℤ)

def fixedReversedTCoeff_17 (n : ℕ) : ℤ :=
    (if 61 = n then (17 : ℤ) else 0) +
    (if 59 = n then (-816 : ℤ) else 0) +
    (if 57 = n then (11424 : ℤ) else 0) +
    (if 55 = n then (-71808 : ℤ) else 0) +
    (if 53 = n then (239360 : ℤ) else 0) +
    (if 51 = n then (-452608 : ℤ) else 0) +
    (if 49 = n then (487424 : ℤ) else 0) +
    (if 47 = n then (-278528 : ℤ) else 0) +
    (if 45 = n then (65536 : ℤ) else 0)

theorem fixed_reversedT_typed_data_17 : reversedRow 63 fixedChebyshevTData_17 = fixedReversedTData_17 := by
  simp only [fixedChebyshevTData_17, fixedReversedTData_17, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (17 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-816 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (11424 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-71808 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (239360 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-452608 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (487424 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-278528 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (65536 : ℤ) 17 (by decide)]

theorem fixed_reversedT_typed_coeff_17 (n : ℕ) :
    fixedReversedTData_17.coeff n = fixedReversedTCoeff_17 n := by
  simp only [fixedReversedTData_17, fixedReversedTCoeff_17, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_17 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_17 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_17, ite_eq_right, add_zero]

def fixedReversedTData_18 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (162 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-4320 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (44352 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-228096 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (658944 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-1118208 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (1105920 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-589824 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (131072 : ℤ)

def fixedReversedTCoeff_18 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (162 : ℤ) else 0) +
    (if 58 = n then (-4320 : ℤ) else 0) +
    (if 56 = n then (44352 : ℤ) else 0) +
    (if 54 = n then (-228096 : ℤ) else 0) +
    (if 52 = n then (658944 : ℤ) else 0) +
    (if 50 = n then (-1118208 : ℤ) else 0) +
    (if 48 = n then (1105920 : ℤ) else 0) +
    (if 46 = n then (-589824 : ℤ) else 0) +
    (if 44 = n then (131072 : ℤ) else 0)

theorem fixed_reversedT_typed_data_18 : reversedRow 63 fixedChebyshevTData_18 = fixedReversedTData_18 := by
  simp only [fixedChebyshevTData_18, fixedReversedTData_18, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (162 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-4320 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (44352 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-228096 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (658944 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-1118208 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (1105920 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-589824 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (131072 : ℤ) 18 (by decide)]

theorem fixed_reversedT_typed_coeff_18 (n : ℕ) :
    fixedReversedTData_18.coeff n = fixedReversedTCoeff_18 n := by
  simp only [fixedReversedTData_18, fixedReversedTCoeff_18, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_18 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_18 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_18, ite_eq_right, add_zero]

def fixedReversedTData_19 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-19 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (1140 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-20064 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (160512 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-695552 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (1770496 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-2723840 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (2490368 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-1245184 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (262144 : ℤ)

def fixedReversedTCoeff_19 (n : ℕ) : ℤ :=
    (if 61 = n then (-19 : ℤ) else 0) +
    (if 59 = n then (1140 : ℤ) else 0) +
    (if 57 = n then (-20064 : ℤ) else 0) +
    (if 55 = n then (160512 : ℤ) else 0) +
    (if 53 = n then (-695552 : ℤ) else 0) +
    (if 51 = n then (1770496 : ℤ) else 0) +
    (if 49 = n then (-2723840 : ℤ) else 0) +
    (if 47 = n then (2490368 : ℤ) else 0) +
    (if 45 = n then (-1245184 : ℤ) else 0) +
    (if 43 = n then (262144 : ℤ) else 0)

theorem fixed_reversedT_typed_data_19 : reversedRow 63 fixedChebyshevTData_19 = fixedReversedTData_19 := by
  simp only [fixedChebyshevTData_19, fixedReversedTData_19, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-19 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (1140 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-20064 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (160512 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-695552 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (1770496 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-2723840 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (2490368 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-1245184 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (262144 : ℤ) 19 (by decide)]

theorem fixed_reversedT_typed_coeff_19 (n : ℕ) :
    fixedReversedTData_19.coeff n = fixedReversedTCoeff_19 n := by
  simp only [fixedReversedTData_19, fixedReversedTCoeff_19, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_19 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_19 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_19, ite_eq_right, add_zero]

def fixedReversedTData_20 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-200 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (6600 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-84480 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (549120 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-2050048 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (4659200 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-6553600 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (5570560 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-2621440 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (524288 : ℤ)

def fixedReversedTCoeff_20 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-200 : ℤ) else 0) +
    (if 58 = n then (6600 : ℤ) else 0) +
    (if 56 = n then (-84480 : ℤ) else 0) +
    (if 54 = n then (549120 : ℤ) else 0) +
    (if 52 = n then (-2050048 : ℤ) else 0) +
    (if 50 = n then (4659200 : ℤ) else 0) +
    (if 48 = n then (-6553600 : ℤ) else 0) +
    (if 46 = n then (5570560 : ℤ) else 0) +
    (if 44 = n then (-2621440 : ℤ) else 0) +
    (if 42 = n then (524288 : ℤ) else 0)

theorem fixed_reversedT_typed_data_20 : reversedRow 63 fixedChebyshevTData_20 = fixedReversedTData_20 := by
  simp only [fixedChebyshevTData_20, fixedReversedTData_20, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-200 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (6600 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-84480 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (549120 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-2050048 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (4659200 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-6553600 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (5570560 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-2621440 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (524288 : ℤ) 20 (by decide)]

theorem fixed_reversedT_typed_coeff_20 (n : ℕ) :
    fixedReversedTData_20.coeff n = fixedReversedTCoeff_20 n := by
  simp only [fixedReversedTData_20, fixedReversedTCoeff_20, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_20 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_20 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_20, ite_eq_right, add_zero]

def fixedReversedTData_21 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (21 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-1540 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (33264 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-329472 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (1793792 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-5870592 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (12042240 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-15597568 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (12386304 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-5505024 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (1048576 : ℤ)

def fixedReversedTCoeff_21 (n : ℕ) : ℤ :=
    (if 61 = n then (21 : ℤ) else 0) +
    (if 59 = n then (-1540 : ℤ) else 0) +
    (if 57 = n then (33264 : ℤ) else 0) +
    (if 55 = n then (-329472 : ℤ) else 0) +
    (if 53 = n then (1793792 : ℤ) else 0) +
    (if 51 = n then (-5870592 : ℤ) else 0) +
    (if 49 = n then (12042240 : ℤ) else 0) +
    (if 47 = n then (-15597568 : ℤ) else 0) +
    (if 45 = n then (12386304 : ℤ) else 0) +
    (if 43 = n then (-5505024 : ℤ) else 0) +
    (if 41 = n then (1048576 : ℤ) else 0)

theorem fixed_reversedT_typed_data_21 : reversedRow 63 fixedChebyshevTData_21 = fixedReversedTData_21 := by
  simp only [fixedChebyshevTData_21, fixedReversedTData_21, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (21 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-1540 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (33264 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-329472 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (1793792 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-5870592 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (12042240 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-15597568 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (12386304 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-5505024 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (1048576 : ℤ) 21 (by decide)]

theorem fixed_reversedT_typed_coeff_21 (n : ℕ) :
    fixedReversedTData_21.coeff n = fixedReversedTCoeff_21 n := by
  simp only [fixedReversedTData_21, fixedReversedTCoeff_21, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_21 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_21 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_21, ite_eq_right, add_zero]

def fixedReversedTData_22 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (242 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-9680 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (151008 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-1208064 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (5637632 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-16400384 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (30638080 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-36765696 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (27394048 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-11534336 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (2097152 : ℤ)

def fixedReversedTCoeff_22 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (242 : ℤ) else 0) +
    (if 58 = n then (-9680 : ℤ) else 0) +
    (if 56 = n then (151008 : ℤ) else 0) +
    (if 54 = n then (-1208064 : ℤ) else 0) +
    (if 52 = n then (5637632 : ℤ) else 0) +
    (if 50 = n then (-16400384 : ℤ) else 0) +
    (if 48 = n then (30638080 : ℤ) else 0) +
    (if 46 = n then (-36765696 : ℤ) else 0) +
    (if 44 = n then (27394048 : ℤ) else 0) +
    (if 42 = n then (-11534336 : ℤ) else 0) +
    (if 40 = n then (2097152 : ℤ) else 0)

theorem fixed_reversedT_typed_data_22 : reversedRow 63 fixedChebyshevTData_22 = fixedReversedTData_22 := by
  simp only [fixedChebyshevTData_22, fixedReversedTData_22, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (242 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-9680 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (151008 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-1208064 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (5637632 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-16400384 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (30638080 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-36765696 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (27394048 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-11534336 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (2097152 : ℤ) 22 (by decide)]

theorem fixed_reversedT_typed_coeff_22 (n : ℕ) :
    fixedReversedTData_22.coeff n = fixedReversedTCoeff_22 n := by
  simp only [fixedReversedTData_22, fixedReversedTCoeff_22, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_22 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_22 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_22, ite_eq_right, add_zero]

def fixedReversedTData_23 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-23 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (2024 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-52624 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (631488 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-4209920 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (17145856 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-44843008 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (76873728 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-85917696 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (60293120 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-24117248 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (4194304 : ℤ)

def fixedReversedTCoeff_23 (n : ℕ) : ℤ :=
    (if 61 = n then (-23 : ℤ) else 0) +
    (if 59 = n then (2024 : ℤ) else 0) +
    (if 57 = n then (-52624 : ℤ) else 0) +
    (if 55 = n then (631488 : ℤ) else 0) +
    (if 53 = n then (-4209920 : ℤ) else 0) +
    (if 51 = n then (17145856 : ℤ) else 0) +
    (if 49 = n then (-44843008 : ℤ) else 0) +
    (if 47 = n then (76873728 : ℤ) else 0) +
    (if 45 = n then (-85917696 : ℤ) else 0) +
    (if 43 = n then (60293120 : ℤ) else 0) +
    (if 41 = n then (-24117248 : ℤ) else 0) +
    (if 39 = n then (4194304 : ℤ) else 0)

theorem fixed_reversedT_typed_data_23 : reversedRow 63 fixedChebyshevTData_23 = fixedReversedTData_23 := by
  simp only [fixedChebyshevTData_23, fixedReversedTData_23, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-23 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (2024 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-52624 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (631488 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-4209920 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (17145856 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-44843008 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (76873728 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-85917696 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (60293120 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-24117248 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (4194304 : ℤ) 23 (by decide)]

theorem fixed_reversedT_typed_coeff_23 (n : ℕ) :
    fixedReversedTData_23.coeff n = fixedReversedTCoeff_23 n := by
  simp only [fixedReversedTData_23, fixedReversedTCoeff_23, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_23 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_23 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_23, ite_eq_right, add_zero]

end InternalCatalan

end

end

end OAI
