import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedUData_16 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-144 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (3360 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-29568 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (126720 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-292864 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (372736 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-245760 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (65536 : ℤ)

def fixedReversedUCoeff_16 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-144 : ℤ) else 0) +
    (if 58 = n then (3360 : ℤ) else 0) +
    (if 56 = n then (-29568 : ℤ) else 0) +
    (if 54 = n then (126720 : ℤ) else 0) +
    (if 52 = n then (-292864 : ℤ) else 0) +
    (if 50 = n then (372736 : ℤ) else 0) +
    (if 48 = n then (-245760 : ℤ) else 0) +
    (if 46 = n then (65536 : ℤ) else 0)

theorem fixed_reversedU_typed_data_16 : reversedRow 63 fixedChebyshevUData_16 = fixedReversedUData_16 := by
  simp only [fixedChebyshevUData_16, fixedReversedUData_16, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-144 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (3360 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-29568 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (126720 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-292864 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (372736 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-245760 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (65536 : ℤ) 16 (by decide)]

theorem fixed_reversedU_typed_coeff_16 (n : ℕ) :
    fixedReversedUData_16.coeff n = fixedReversedUCoeff_16 n := by
  simp only [fixedReversedUData_16, fixedReversedUCoeff_16, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_16 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_16 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_16, ite_eq_right, add_zero]

def fixedReversedUData_17 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (18 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-960 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (14784 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-101376 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (366080 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-745472 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (860160 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-524288 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (131072 : ℤ)

def fixedReversedUCoeff_17 (n : ℕ) : ℤ :=
    (if 61 = n then (18 : ℤ) else 0) +
    (if 59 = n then (-960 : ℤ) else 0) +
    (if 57 = n then (14784 : ℤ) else 0) +
    (if 55 = n then (-101376 : ℤ) else 0) +
    (if 53 = n then (366080 : ℤ) else 0) +
    (if 51 = n then (-745472 : ℤ) else 0) +
    (if 49 = n then (860160 : ℤ) else 0) +
    (if 47 = n then (-524288 : ℤ) else 0) +
    (if 45 = n then (131072 : ℤ) else 0)

theorem fixed_reversedU_typed_data_17 : reversedRow 63 fixedChebyshevUData_17 = fixedReversedUData_17 := by
  simp only [fixedChebyshevUData_17, fixedReversedUData_17, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (18 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-960 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (14784 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-101376 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (366080 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-745472 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (860160 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-524288 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (131072 : ℤ) 17 (by decide)]

theorem fixed_reversedU_typed_coeff_17 (n : ℕ) :
    fixedReversedUData_17.coeff n = fixedReversedUCoeff_17 n := by
  simp only [fixedReversedUData_17, fixedReversedUCoeff_17, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_17 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_17 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_17, ite_eq_right, add_zero]

def fixedReversedUData_18 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (180 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-5280 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (59136 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-329472 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (1025024 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-1863680 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (1966080 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-1114112 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (262144 : ℤ)

def fixedReversedUCoeff_18 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (180 : ℤ) else 0) +
    (if 58 = n then (-5280 : ℤ) else 0) +
    (if 56 = n then (59136 : ℤ) else 0) +
    (if 54 = n then (-329472 : ℤ) else 0) +
    (if 52 = n then (1025024 : ℤ) else 0) +
    (if 50 = n then (-1863680 : ℤ) else 0) +
    (if 48 = n then (1966080 : ℤ) else 0) +
    (if 46 = n then (-1114112 : ℤ) else 0) +
    (if 44 = n then (262144 : ℤ) else 0)

theorem fixed_reversedU_typed_data_18 : reversedRow 63 fixedChebyshevUData_18 = fixedReversedUData_18 := by
  simp only [fixedChebyshevUData_18, fixedReversedUData_18, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (180 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-5280 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (59136 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-329472 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (1025024 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-1863680 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (1966080 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-1114112 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (262144 : ℤ) 18 (by decide)]

theorem fixed_reversedU_typed_coeff_18 (n : ℕ) :
    fixedReversedUData_18.coeff n = fixedReversedUCoeff_18 n := by
  simp only [fixedReversedUData_18, fixedReversedUCoeff_18, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_18 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_18 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_18, ite_eq_right, add_zero]

def fixedReversedUData_19 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-20 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (1320 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-25344 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (219648 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1025024 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (2795520 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-4587520 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (4456448 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-2359296 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (524288 : ℤ)

def fixedReversedUCoeff_19 (n : ℕ) : ℤ :=
    (if 61 = n then (-20 : ℤ) else 0) +
    (if 59 = n then (1320 : ℤ) else 0) +
    (if 57 = n then (-25344 : ℤ) else 0) +
    (if 55 = n then (219648 : ℤ) else 0) +
    (if 53 = n then (-1025024 : ℤ) else 0) +
    (if 51 = n then (2795520 : ℤ) else 0) +
    (if 49 = n then (-4587520 : ℤ) else 0) +
    (if 47 = n then (4456448 : ℤ) else 0) +
    (if 45 = n then (-2359296 : ℤ) else 0) +
    (if 43 = n then (524288 : ℤ) else 0)

theorem fixed_reversedU_typed_data_19 : reversedRow 63 fixedChebyshevUData_19 = fixedReversedUData_19 := by
  simp only [fixedChebyshevUData_19, fixedReversedUData_19, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-20 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (1320 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-25344 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (219648 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-1025024 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (2795520 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-4587520 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (4456448 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-2359296 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (524288 : ℤ) 19 (by decide)]

theorem fixed_reversedU_typed_coeff_19 (n : ℕ) :
    fixedReversedUData_19.coeff n = fixedReversedUCoeff_19 n := by
  simp only [fixedReversedUData_19, fixedReversedUCoeff_19, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_19 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_19 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_19, ite_eq_right, add_zero]

def fixedReversedUData_20 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-220 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (7920 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-109824 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (768768 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-3075072 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (7454720 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-11141120 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (10027008 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-4980736 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (1048576 : ℤ)

def fixedReversedUCoeff_20 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-220 : ℤ) else 0) +
    (if 58 = n then (7920 : ℤ) else 0) +
    (if 56 = n then (-109824 : ℤ) else 0) +
    (if 54 = n then (768768 : ℤ) else 0) +
    (if 52 = n then (-3075072 : ℤ) else 0) +
    (if 50 = n then (7454720 : ℤ) else 0) +
    (if 48 = n then (-11141120 : ℤ) else 0) +
    (if 46 = n then (10027008 : ℤ) else 0) +
    (if 44 = n then (-4980736 : ℤ) else 0) +
    (if 42 = n then (1048576 : ℤ) else 0)

theorem fixed_reversedU_typed_data_20 : reversedRow 63 fixedChebyshevUData_20 = fixedReversedUData_20 := by
  simp only [fixedChebyshevUData_20, fixedReversedUData_20, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-220 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (7920 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-109824 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (768768 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-3075072 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (7454720 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-11141120 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (10027008 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-4980736 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (1048576 : ℤ) 20 (by decide)]

theorem fixed_reversedU_typed_coeff_20 (n : ℕ) :
    fixedReversedUData_20.coeff n = fixedReversedUCoeff_20 n := by
  simp only [fixedReversedUData_20, fixedReversedUCoeff_20, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_20 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_20 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_20, ite_eq_right, add_zero]

def fixedReversedUData_21 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (22 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-1760 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (41184 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-439296 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (2562560 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-8945664 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (19496960 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-26738688 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (22413312 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-10485760 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (2097152 : ℤ)

def fixedReversedUCoeff_21 (n : ℕ) : ℤ :=
    (if 61 = n then (22 : ℤ) else 0) +
    (if 59 = n then (-1760 : ℤ) else 0) +
    (if 57 = n then (41184 : ℤ) else 0) +
    (if 55 = n then (-439296 : ℤ) else 0) +
    (if 53 = n then (2562560 : ℤ) else 0) +
    (if 51 = n then (-8945664 : ℤ) else 0) +
    (if 49 = n then (19496960 : ℤ) else 0) +
    (if 47 = n then (-26738688 : ℤ) else 0) +
    (if 45 = n then (22413312 : ℤ) else 0) +
    (if 43 = n then (-10485760 : ℤ) else 0) +
    (if 41 = n then (2097152 : ℤ) else 0)

theorem fixed_reversedU_typed_data_21 : reversedRow 63 fixedChebyshevUData_21 = fixedReversedUData_21 := by
  simp only [fixedChebyshevUData_21, fixedReversedUData_21, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (22 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-1760 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (41184 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-439296 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (2562560 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-8945664 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (19496960 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-26738688 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (22413312 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-10485760 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (2097152 : ℤ) 21 (by decide)]

theorem fixed_reversedU_typed_coeff_21 (n : ℕ) :
    fixedReversedUData_21.coeff n = fixedReversedUCoeff_21 n := by
  simp only [fixedReversedUData_21, fixedReversedUCoeff_21, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_21 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_21 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_21, ite_eq_right, add_zero]

def fixedReversedUData_22 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (264 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-11440 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (192192 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-1647360 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (8200192 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-25346048 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (50135040 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-63504384 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (49807360 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-22020096 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (4194304 : ℤ)

def fixedReversedUCoeff_22 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (264 : ℤ) else 0) +
    (if 58 = n then (-11440 : ℤ) else 0) +
    (if 56 = n then (192192 : ℤ) else 0) +
    (if 54 = n then (-1647360 : ℤ) else 0) +
    (if 52 = n then (8200192 : ℤ) else 0) +
    (if 50 = n then (-25346048 : ℤ) else 0) +
    (if 48 = n then (50135040 : ℤ) else 0) +
    (if 46 = n then (-63504384 : ℤ) else 0) +
    (if 44 = n then (49807360 : ℤ) else 0) +
    (if 42 = n then (-22020096 : ℤ) else 0) +
    (if 40 = n then (4194304 : ℤ) else 0)

theorem fixed_reversedU_typed_data_22 : reversedRow 63 fixedChebyshevUData_22 = fixedReversedUData_22 := by
  simp only [fixedChebyshevUData_22, fixedReversedUData_22, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (264 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-11440 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (192192 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-1647360 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (8200192 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-25346048 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (50135040 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-63504384 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (49807360 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-22020096 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (4194304 : ℤ) 22 (by decide)]

theorem fixed_reversedU_typed_coeff_22 (n : ℕ) :
    fixedReversedUData_22.coeff n = fixedReversedUCoeff_22 n := by
  simp only [fixedReversedUData_22, fixedReversedUCoeff_22, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_22 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_22 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_22, ite_eq_right, add_zero]

def fixedReversedUData_23 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-24 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (2288 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-64064 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (823680 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-5857280 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (25346048 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-70189056 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (127008768 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-149422080 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (110100480 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-46137344 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (8388608 : ℤ)

def fixedReversedUCoeff_23 (n : ℕ) : ℤ :=
    (if 61 = n then (-24 : ℤ) else 0) +
    (if 59 = n then (2288 : ℤ) else 0) +
    (if 57 = n then (-64064 : ℤ) else 0) +
    (if 55 = n then (823680 : ℤ) else 0) +
    (if 53 = n then (-5857280 : ℤ) else 0) +
    (if 51 = n then (25346048 : ℤ) else 0) +
    (if 49 = n then (-70189056 : ℤ) else 0) +
    (if 47 = n then (127008768 : ℤ) else 0) +
    (if 45 = n then (-149422080 : ℤ) else 0) +
    (if 43 = n then (110100480 : ℤ) else 0) +
    (if 41 = n then (-46137344 : ℤ) else 0) +
    (if 39 = n then (8388608 : ℤ) else 0)

theorem fixed_reversedU_typed_data_23 : reversedRow 63 fixedChebyshevUData_23 = fixedReversedUData_23 := by
  simp only [fixedChebyshevUData_23, fixedReversedUData_23, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-24 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (2288 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-64064 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (823680 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-5857280 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (25346048 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-70189056 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (127008768 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-149422080 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (110100480 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-46137344 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (8388608 : ℤ) 23 (by decide)]

theorem fixed_reversedU_typed_coeff_23 (n : ℕ) :
    fixedReversedUData_23.coeff n = fixedReversedUCoeff_23 n := by
  simp only [fixedReversedUData_23, fixedReversedUCoeff_23, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_23 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_23 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_23, ite_eq_right, add_zero]

end InternalCatalan

end

end

end OAI
