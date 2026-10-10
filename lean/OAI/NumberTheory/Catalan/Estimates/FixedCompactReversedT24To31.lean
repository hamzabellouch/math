import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedTData_24 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-288 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (13728 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-256256 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (2471040 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-14057472 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (50692096 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-120324096 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (190513152 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-199229440 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (132120576 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-50331648 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (8388608 : ℤ)

def fixedReversedTCoeff_24 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-288 : ℤ) else 0) +
    (if 58 = n then (13728 : ℤ) else 0) +
    (if 56 = n then (-256256 : ℤ) else 0) +
    (if 54 = n then (2471040 : ℤ) else 0) +
    (if 52 = n then (-14057472 : ℤ) else 0) +
    (if 50 = n then (50692096 : ℤ) else 0) +
    (if 48 = n then (-120324096 : ℤ) else 0) +
    (if 46 = n then (190513152 : ℤ) else 0) +
    (if 44 = n then (-199229440 : ℤ) else 0) +
    (if 42 = n then (132120576 : ℤ) else 0) +
    (if 40 = n then (-50331648 : ℤ) else 0) +
    (if 38 = n then (8388608 : ℤ) else 0)

theorem fixed_reversedT_typed_data_24 : reversedRow 63 fixedChebyshevTData_24 = fixedReversedTData_24 := by
  simp only [fixedChebyshevTData_24, fixedReversedTData_24, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-288 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (13728 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-256256 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (2471040 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-14057472 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (50692096 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-120324096 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (190513152 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-199229440 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (132120576 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-50331648 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (8388608 : ℤ) 24 (by decide)]

theorem fixed_reversedT_typed_coeff_24 (n : ℕ) :
    fixedReversedTData_24.coeff n = fixedReversedTCoeff_24 n := by
  simp only [fixedReversedTData_24, fixedReversedTCoeff_24, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_24 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_24 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_24, ite_eq_right, add_zero]

def fixedReversedTData_25 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (25 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-2600 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (80080 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-1144000 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (9152000 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-45260800 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (146227200 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-317521920 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (466944000 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-458752000 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (288358400 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-104857600 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (16777216 : ℤ)

def fixedReversedTCoeff_25 (n : ℕ) : ℤ :=
    (if 61 = n then (25 : ℤ) else 0) +
    (if 59 = n then (-2600 : ℤ) else 0) +
    (if 57 = n then (80080 : ℤ) else 0) +
    (if 55 = n then (-1144000 : ℤ) else 0) +
    (if 53 = n then (9152000 : ℤ) else 0) +
    (if 51 = n then (-45260800 : ℤ) else 0) +
    (if 49 = n then (146227200 : ℤ) else 0) +
    (if 47 = n then (-317521920 : ℤ) else 0) +
    (if 45 = n then (466944000 : ℤ) else 0) +
    (if 43 = n then (-458752000 : ℤ) else 0) +
    (if 41 = n then (288358400 : ℤ) else 0) +
    (if 39 = n then (-104857600 : ℤ) else 0) +
    (if 37 = n then (16777216 : ℤ) else 0)

theorem fixed_reversedT_typed_data_25 : reversedRow 63 fixedChebyshevTData_25 = fixedReversedTData_25 := by
  simp only [fixedChebyshevTData_25, fixedReversedTData_25, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (25 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-2600 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (80080 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-1144000 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (9152000 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-45260800 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (146227200 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-317521920 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (466944000 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-458752000 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (288358400 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-104857600 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (16777216 : ℤ) 25 (by decide)]

theorem fixed_reversedT_typed_coeff_25 (n : ℕ) :
    fixedReversedTData_25.coeff n = fixedReversedTCoeff_25 n := by
  simp only [fixedReversedTData_25, fixedReversedTCoeff_25, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_25 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_25 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_25, ite_eq_right, add_zero]

def fixedReversedTData_26 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (338 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-18928 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (416416 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-4759040 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (32361472 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-141213696 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (412778496 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-825556992 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (1133117440 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-1049624576 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (627048448 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-218103808 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (33554432 : ℤ)

def fixedReversedTCoeff_26 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (338 : ℤ) else 0) +
    (if 58 = n then (-18928 : ℤ) else 0) +
    (if 56 = n then (416416 : ℤ) else 0) +
    (if 54 = n then (-4759040 : ℤ) else 0) +
    (if 52 = n then (32361472 : ℤ) else 0) +
    (if 50 = n then (-141213696 : ℤ) else 0) +
    (if 48 = n then (412778496 : ℤ) else 0) +
    (if 46 = n then (-825556992 : ℤ) else 0) +
    (if 44 = n then (1133117440 : ℤ) else 0) +
    (if 42 = n then (-1049624576 : ℤ) else 0) +
    (if 40 = n then (627048448 : ℤ) else 0) +
    (if 38 = n then (-218103808 : ℤ) else 0) +
    (if 36 = n then (33554432 : ℤ) else 0)

theorem fixed_reversedT_typed_data_26 : reversedRow 63 fixedChebyshevTData_26 = fixedReversedTData_26 := by
  simp only [fixedChebyshevTData_26, fixedReversedTData_26, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (338 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-18928 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (416416 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-4759040 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (32361472 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-141213696 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (412778496 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-825556992 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (1133117440 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-1049624576 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (627048448 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-218103808 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (33554432 : ℤ) 26 (by decide)]

theorem fixed_reversedT_typed_coeff_26 (n : ℕ) :
    fixedReversedTData_26.coeff n = fixedReversedTCoeff_26 n := by
  simp only [fixedReversedTData_26, fixedReversedTCoeff_26, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_26 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_26 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_26, ite_eq_right, add_zero]

def fixedReversedTData_27 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-27 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (3276 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-117936 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (1976832 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-18670080 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (109983744 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-428654592 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (1143078912 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-2118057984 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (2724986880 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-2387607552 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (1358954496 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-452984832 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (67108864 : ℤ)

def fixedReversedTCoeff_27 (n : ℕ) : ℤ :=
    (if 61 = n then (-27 : ℤ) else 0) +
    (if 59 = n then (3276 : ℤ) else 0) +
    (if 57 = n then (-117936 : ℤ) else 0) +
    (if 55 = n then (1976832 : ℤ) else 0) +
    (if 53 = n then (-18670080 : ℤ) else 0) +
    (if 51 = n then (109983744 : ℤ) else 0) +
    (if 49 = n then (-428654592 : ℤ) else 0) +
    (if 47 = n then (1143078912 : ℤ) else 0) +
    (if 45 = n then (-2118057984 : ℤ) else 0) +
    (if 43 = n then (2724986880 : ℤ) else 0) +
    (if 41 = n then (-2387607552 : ℤ) else 0) +
    (if 39 = n then (1358954496 : ℤ) else 0) +
    (if 37 = n then (-452984832 : ℤ) else 0) +
    (if 35 = n then (67108864 : ℤ) else 0)

theorem fixed_reversedT_typed_data_27 : reversedRow 63 fixedChebyshevTData_27 = fixedReversedTData_27 := by
  simp only [fixedChebyshevTData_27, fixedReversedTData_27, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-27 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (3276 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-117936 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (1976832 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-18670080 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (109983744 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-428654592 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (1143078912 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-2118057984 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (2724986880 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-2387607552 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (1358954496 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-452984832 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (67108864 : ℤ) 27 (by decide)]

theorem fixed_reversedT_typed_coeff_27 (n : ℕ) :
    fixedReversedTData_27.coeff n = fixedReversedTCoeff_27 n := by
  simp only [fixedReversedTData_27, fixedReversedTCoeff_27, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_27 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_27 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_27, ite_eq_right, add_zero]

def fixedReversedTData_28 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-392 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (25480 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-652288 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (8712704 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-69701632 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (361181184 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-1270087680 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (3111714816 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-5369233408 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (6499598336 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-5402263552 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (2936012800 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-939524096 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (134217728 : ℤ)

def fixedReversedTCoeff_28 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-392 : ℤ) else 0) +
    (if 58 = n then (25480 : ℤ) else 0) +
    (if 56 = n then (-652288 : ℤ) else 0) +
    (if 54 = n then (8712704 : ℤ) else 0) +
    (if 52 = n then (-69701632 : ℤ) else 0) +
    (if 50 = n then (361181184 : ℤ) else 0) +
    (if 48 = n then (-1270087680 : ℤ) else 0) +
    (if 46 = n then (3111714816 : ℤ) else 0) +
    (if 44 = n then (-5369233408 : ℤ) else 0) +
    (if 42 = n then (6499598336 : ℤ) else 0) +
    (if 40 = n then (-5402263552 : ℤ) else 0) +
    (if 38 = n then (2936012800 : ℤ) else 0) +
    (if 36 = n then (-939524096 : ℤ) else 0) +
    (if 34 = n then (134217728 : ℤ) else 0)

theorem fixed_reversedT_typed_data_28 : reversedRow 63 fixedChebyshevTData_28 = fixedReversedTData_28 := by
  simp only [fixedChebyshevTData_28, fixedReversedTData_28, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-392 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (25480 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-652288 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (8712704 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-69701632 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (361181184 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-1270087680 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (3111714816 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-5369233408 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (6499598336 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-5402263552 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (2936012800 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-939524096 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (134217728 : ℤ) 28 (by decide)]

theorem fixed_reversedT_typed_coeff_28 (n : ℕ) :
    fixedReversedTData_28.coeff n = fixedReversedTCoeff_28 n := by
  simp only [fixedReversedTData_28, fixedReversedTCoeff_28, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_28 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_28 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_28, ite_eq_right, add_zero]

def fixedReversedTData_29 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (29 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-4060 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (168896 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-3281408 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (36095488 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-249387008 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (1151016960 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-3683254272 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (8341487616 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-13463453696 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (15386804224 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-12163481600 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (6325010432 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-1946157056 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (268435456 : ℤ)

def fixedReversedTCoeff_29 (n : ℕ) : ℤ :=
    (if 61 = n then (29 : ℤ) else 0) +
    (if 59 = n then (-4060 : ℤ) else 0) +
    (if 57 = n then (168896 : ℤ) else 0) +
    (if 55 = n then (-3281408 : ℤ) else 0) +
    (if 53 = n then (36095488 : ℤ) else 0) +
    (if 51 = n then (-249387008 : ℤ) else 0) +
    (if 49 = n then (1151016960 : ℤ) else 0) +
    (if 47 = n then (-3683254272 : ℤ) else 0) +
    (if 45 = n then (8341487616 : ℤ) else 0) +
    (if 43 = n then (-13463453696 : ℤ) else 0) +
    (if 41 = n then (15386804224 : ℤ) else 0) +
    (if 39 = n then (-12163481600 : ℤ) else 0) +
    (if 37 = n then (6325010432 : ℤ) else 0) +
    (if 35 = n then (-1946157056 : ℤ) else 0) +
    (if 33 = n then (268435456 : ℤ) else 0)

theorem fixed_reversedT_typed_data_29 : reversedRow 63 fixedChebyshevTData_29 = fixedReversedTData_29 := by
  simp only [fixedChebyshevTData_29, fixedReversedTData_29, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (29 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-4060 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (168896 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-3281408 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (36095488 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-249387008 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (1151016960 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-3683254272 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (8341487616 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-13463453696 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (15386804224 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-12163481600 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (6325010432 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (-1946157056 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (268435456 : ℤ) 29 (by decide)]

theorem fixed_reversedT_typed_coeff_29 (n : ℕ) :
    fixedReversedTData_29.coeff n = fixedReversedTCoeff_29 n := by
  simp only [fixedReversedTData_29, fixedReversedTCoeff_29, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_29 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_29 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_29, ite_eq_right, add_zero]

def fixedReversedTData_30 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (450 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-33600 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (990080 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-15275520 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (141892608 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-859955200 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (3572121600 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-10478223360 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (22052208640 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-33426505728 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (36175872000 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-27262976000 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (13589544960 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-4026531840 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (536870912 : ℤ)

def fixedReversedTCoeff_30 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (450 : ℤ) else 0) +
    (if 58 = n then (-33600 : ℤ) else 0) +
    (if 56 = n then (990080 : ℤ) else 0) +
    (if 54 = n then (-15275520 : ℤ) else 0) +
    (if 52 = n then (141892608 : ℤ) else 0) +
    (if 50 = n then (-859955200 : ℤ) else 0) +
    (if 48 = n then (3572121600 : ℤ) else 0) +
    (if 46 = n then (-10478223360 : ℤ) else 0) +
    (if 44 = n then (22052208640 : ℤ) else 0) +
    (if 42 = n then (-33426505728 : ℤ) else 0) +
    (if 40 = n then (36175872000 : ℤ) else 0) +
    (if 38 = n then (-27262976000 : ℤ) else 0) +
    (if 36 = n then (13589544960 : ℤ) else 0) +
    (if 34 = n then (-4026531840 : ℤ) else 0) +
    (if 32 = n then (536870912 : ℤ) else 0)

theorem fixed_reversedT_typed_data_30 : reversedRow 63 fixedChebyshevTData_30 = fixedReversedTData_30 := by
  simp only [fixedChebyshevTData_30, fixedReversedTData_30, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (450 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-33600 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (990080 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-15275520 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (141892608 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-859955200 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (3572121600 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-10478223360 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (22052208640 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-33426505728 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (36175872000 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-27262976000 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (13589544960 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (-4026531840 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (536870912 : ℤ) 30 (by decide)]

theorem fixed_reversedT_typed_coeff_30 (n : ℕ) :
    fixedReversedTData_30.coeff n = fixedReversedTCoeff_30 n := by
  simp only [fixedReversedTData_30, fixedReversedTCoeff_30, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_30 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_30 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_30, ite_eq_right, add_zero]

def fixedReversedTData_31 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-31 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (4960 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-236096 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (5261568 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-66646528 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (533172224 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-2870927360 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (10827497472 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-29297934336 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (57567870976 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-82239815680 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (84515225600 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-60850962432 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (29125246976 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-8321499136 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (1073741824 : ℤ)

def fixedReversedTCoeff_31 (n : ℕ) : ℤ :=
    (if 61 = n then (-31 : ℤ) else 0) +
    (if 59 = n then (4960 : ℤ) else 0) +
    (if 57 = n then (-236096 : ℤ) else 0) +
    (if 55 = n then (5261568 : ℤ) else 0) +
    (if 53 = n then (-66646528 : ℤ) else 0) +
    (if 51 = n then (533172224 : ℤ) else 0) +
    (if 49 = n then (-2870927360 : ℤ) else 0) +
    (if 47 = n then (10827497472 : ℤ) else 0) +
    (if 45 = n then (-29297934336 : ℤ) else 0) +
    (if 43 = n then (57567870976 : ℤ) else 0) +
    (if 41 = n then (-82239815680 : ℤ) else 0) +
    (if 39 = n then (84515225600 : ℤ) else 0) +
    (if 37 = n then (-60850962432 : ℤ) else 0) +
    (if 35 = n then (29125246976 : ℤ) else 0) +
    (if 33 = n then (-8321499136 : ℤ) else 0) +
    (if 31 = n then (1073741824 : ℤ) else 0)

theorem fixed_reversedT_typed_data_31 : reversedRow 63 fixedChebyshevTData_31 = fixedReversedTData_31 := by
  simp only [fixedChebyshevTData_31, fixedReversedTData_31, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-31 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (4960 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-236096 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (5261568 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-66646528 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (533172224 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-2870927360 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (10827497472 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-29297934336 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (57567870976 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-82239815680 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (84515225600 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-60850962432 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (29125246976 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (-8321499136 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (1073741824 : ℤ) 31 (by decide)]

theorem fixed_reversedT_typed_coeff_31 (n : ℕ) :
    fixedReversedTData_31.coeff n = fixedReversedTCoeff_31 n := by
  simp only [fixedReversedTData_31, fixedReversedTCoeff_31, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_31 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_31 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_31, ite_eq_right, add_zero]

end InternalCatalan

end

end

end OAI
