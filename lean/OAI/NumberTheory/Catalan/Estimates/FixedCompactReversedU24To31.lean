import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedUData_24 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-312 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (16016 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-320320 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (3294720 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-19914752 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (76038144 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-190513152 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (317521920 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-348651520 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (242221056 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-96468992 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (16777216 : ℤ)

def fixedReversedUCoeff_24 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-312 : ℤ) else 0) +
    (if 58 = n then (16016 : ℤ) else 0) +
    (if 56 = n then (-320320 : ℤ) else 0) +
    (if 54 = n then (3294720 : ℤ) else 0) +
    (if 52 = n then (-19914752 : ℤ) else 0) +
    (if 50 = n then (76038144 : ℤ) else 0) +
    (if 48 = n then (-190513152 : ℤ) else 0) +
    (if 46 = n then (317521920 : ℤ) else 0) +
    (if 44 = n then (-348651520 : ℤ) else 0) +
    (if 42 = n then (242221056 : ℤ) else 0) +
    (if 40 = n then (-96468992 : ℤ) else 0) +
    (if 38 = n then (16777216 : ℤ) else 0)

theorem fixed_reversedU_typed_data_24 : reversedRow 63 fixedChebyshevUData_24 = fixedReversedUData_24 := by
  simp only [fixedChebyshevUData_24, fixedReversedUData_24, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-312 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (16016 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-320320 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (3294720 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-19914752 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (76038144 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-190513152 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (317521920 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-348651520 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (242221056 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-96468992 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (16777216 : ℤ) 24 (by decide)]

theorem fixed_reversedU_typed_coeff_24 (n : ℕ) :
    fixedReversedUData_24.coeff n = fixedReversedUCoeff_24 n := by
  simp only [fixedReversedUData_24, fixedReversedUCoeff_24, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_24 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_24 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_24, ite_eq_right, add_zero]

def fixedReversedUData_25 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (26 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-2912 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (96096 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-1464320 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (12446720 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-65175552 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (222265344 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-508035072 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (784465920 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-807403520 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (530579456 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-201326592 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (33554432 : ℤ)

def fixedReversedUCoeff_25 (n : ℕ) : ℤ :=
    (if 61 = n then (26 : ℤ) else 0) +
    (if 59 = n then (-2912 : ℤ) else 0) +
    (if 57 = n then (96096 : ℤ) else 0) +
    (if 55 = n then (-1464320 : ℤ) else 0) +
    (if 53 = n then (12446720 : ℤ) else 0) +
    (if 51 = n then (-65175552 : ℤ) else 0) +
    (if 49 = n then (222265344 : ℤ) else 0) +
    (if 47 = n then (-508035072 : ℤ) else 0) +
    (if 45 = n then (784465920 : ℤ) else 0) +
    (if 43 = n then (-807403520 : ℤ) else 0) +
    (if 41 = n then (530579456 : ℤ) else 0) +
    (if 39 = n then (-201326592 : ℤ) else 0) +
    (if 37 = n then (33554432 : ℤ) else 0)

theorem fixed_reversedU_typed_data_25 : reversedRow 63 fixedChebyshevUData_25 = fixedReversedUData_25 := by
  simp only [fixedChebyshevUData_25, fixedReversedUData_25, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (26 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-2912 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (96096 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-1464320 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (12446720 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-65175552 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (222265344 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-508035072 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (784465920 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-807403520 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (530579456 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-201326592 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (33554432 : ℤ) 25 (by decide)]

theorem fixed_reversedU_typed_coeff_25 (n : ℕ) :
    fixedReversedUData_25.coeff n = fixedReversedUCoeff_25 n := by
  simp only [fixedReversedUData_25, fixedReversedUCoeff_25, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_25 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_25 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_25, ite_eq_right, add_zero]

def fixedReversedUData_26 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (364 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-21840 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (512512 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-6223360 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (44808192 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-206389248 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (635043840 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-1333592064 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (1917583360 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-1857028096 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (1157627904 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-419430400 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (67108864 : ℤ)

def fixedReversedUCoeff_26 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (364 : ℤ) else 0) +
    (if 58 = n then (-21840 : ℤ) else 0) +
    (if 56 = n then (512512 : ℤ) else 0) +
    (if 54 = n then (-6223360 : ℤ) else 0) +
    (if 52 = n then (44808192 : ℤ) else 0) +
    (if 50 = n then (-206389248 : ℤ) else 0) +
    (if 48 = n then (635043840 : ℤ) else 0) +
    (if 46 = n then (-1333592064 : ℤ) else 0) +
    (if 44 = n then (1917583360 : ℤ) else 0) +
    (if 42 = n then (-1857028096 : ℤ) else 0) +
    (if 40 = n then (1157627904 : ℤ) else 0) +
    (if 38 = n then (-419430400 : ℤ) else 0) +
    (if 36 = n then (67108864 : ℤ) else 0)

theorem fixed_reversedU_typed_data_26 : reversedRow 63 fixedChebyshevUData_26 = fixedReversedUData_26 := by
  simp only [fixedChebyshevUData_26, fixedReversedUData_26, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (364 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-21840 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (512512 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-6223360 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (44808192 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-206389248 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (635043840 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-1333592064 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (1917583360 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-1857028096 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (1157627904 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-419430400 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (67108864 : ℤ) 26 (by decide)]

theorem fixed_reversedU_typed_coeff_26 (n : ℕ) :
    fixedReversedUData_26.coeff n = fixedReversedUCoeff_26 n := by
  simp only [fixedReversedUData_26, fixedReversedUCoeff_26, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_26 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_26 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_26, ite_eq_right, add_zero]

def fixedReversedUData_27 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-28 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (3640 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-139776 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (2489344 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-24893440 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (154791936 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-635043840 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (1778122752 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-3451650048 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (4642570240 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-4244635648 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (2516582400 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-872415232 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (134217728 : ℤ)

def fixedReversedUCoeff_27 (n : ℕ) : ℤ :=
    (if 61 = n then (-28 : ℤ) else 0) +
    (if 59 = n then (3640 : ℤ) else 0) +
    (if 57 = n then (-139776 : ℤ) else 0) +
    (if 55 = n then (2489344 : ℤ) else 0) +
    (if 53 = n then (-24893440 : ℤ) else 0) +
    (if 51 = n then (154791936 : ℤ) else 0) +
    (if 49 = n then (-635043840 : ℤ) else 0) +
    (if 47 = n then (1778122752 : ℤ) else 0) +
    (if 45 = n then (-3451650048 : ℤ) else 0) +
    (if 43 = n then (4642570240 : ℤ) else 0) +
    (if 41 = n then (-4244635648 : ℤ) else 0) +
    (if 39 = n then (2516582400 : ℤ) else 0) +
    (if 37 = n then (-872415232 : ℤ) else 0) +
    (if 35 = n then (134217728 : ℤ) else 0)

theorem fixed_reversedU_typed_data_27 : reversedRow 63 fixedChebyshevUData_27 = fixedReversedUData_27 := by
  simp only [fixedChebyshevUData_27, fixedReversedUData_27, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-28 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (3640 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-139776 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (2489344 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-24893440 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (154791936 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-635043840 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (1778122752 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-3451650048 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (4642570240 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-4244635648 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (2516582400 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-872415232 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (134217728 : ℤ) 27 (by decide)]

theorem fixed_reversedU_typed_coeff_27 (n : ℕ) :
    fixedReversedUData_27.coeff n = fixedReversedUCoeff_27 n := by
  simp only [fixedReversedUData_27, fixedReversedUCoeff_27, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_27 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_27 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_27, ite_eq_right, add_zero]

def fixedReversedUData_28 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-420 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (29120 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-792064 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (11202048 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-94595072 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (515973120 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-1905131520 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (4889837568 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-8820883456 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (11142168576 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-9646899200 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (5452595200 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-1811939328 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (268435456 : ℤ)

def fixedReversedUCoeff_28 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-420 : ℤ) else 0) +
    (if 58 = n then (29120 : ℤ) else 0) +
    (if 56 = n then (-792064 : ℤ) else 0) +
    (if 54 = n then (11202048 : ℤ) else 0) +
    (if 52 = n then (-94595072 : ℤ) else 0) +
    (if 50 = n then (515973120 : ℤ) else 0) +
    (if 48 = n then (-1905131520 : ℤ) else 0) +
    (if 46 = n then (4889837568 : ℤ) else 0) +
    (if 44 = n then (-8820883456 : ℤ) else 0) +
    (if 42 = n then (11142168576 : ℤ) else 0) +
    (if 40 = n then (-9646899200 : ℤ) else 0) +
    (if 38 = n then (5452595200 : ℤ) else 0) +
    (if 36 = n then (-1811939328 : ℤ) else 0) +
    (if 34 = n then (268435456 : ℤ) else 0)

theorem fixed_reversedU_typed_data_28 : reversedRow 63 fixedChebyshevUData_28 = fixedReversedUData_28 := by
  simp only [fixedChebyshevUData_28, fixedReversedUData_28, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-420 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (29120 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-792064 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (11202048 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-94595072 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (515973120 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-1905131520 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (4889837568 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-8820883456 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (11142168576 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-9646899200 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (5452595200 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-1811939328 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (268435456 : ℤ) 28 (by decide)]

theorem fixed_reversedU_typed_coeff_28 (n : ℕ) :
    fixedReversedUData_28.coeff n = fixedReversedUCoeff_28 n := by
  simp only [fixedReversedUData_28, fixedReversedUCoeff_28, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_28 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_28 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_28, ite_eq_right, add_zero]

def fixedReversedUData_29 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (30 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-4480 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (198016 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-4073472 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (47297536 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-343982080 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (1666990080 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-5588385792 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (13231325184 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-22284337152 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (26528972800 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-21810380800 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (11777605632 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-3758096384 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (536870912 : ℤ)

def fixedReversedUCoeff_29 (n : ℕ) : ℤ :=
    (if 61 = n then (30 : ℤ) else 0) +
    (if 59 = n then (-4480 : ℤ) else 0) +
    (if 57 = n then (198016 : ℤ) else 0) +
    (if 55 = n then (-4073472 : ℤ) else 0) +
    (if 53 = n then (47297536 : ℤ) else 0) +
    (if 51 = n then (-343982080 : ℤ) else 0) +
    (if 49 = n then (1666990080 : ℤ) else 0) +
    (if 47 = n then (-5588385792 : ℤ) else 0) +
    (if 45 = n then (13231325184 : ℤ) else 0) +
    (if 43 = n then (-22284337152 : ℤ) else 0) +
    (if 41 = n then (26528972800 : ℤ) else 0) +
    (if 39 = n then (-21810380800 : ℤ) else 0) +
    (if 37 = n then (11777605632 : ℤ) else 0) +
    (if 35 = n then (-3758096384 : ℤ) else 0) +
    (if 33 = n then (536870912 : ℤ) else 0)

theorem fixed_reversedU_typed_data_29 : reversedRow 63 fixedChebyshevUData_29 = fixedReversedUData_29 := by
  simp only [fixedChebyshevUData_29, fixedReversedUData_29, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (30 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-4480 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (198016 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-4073472 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (47297536 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-343982080 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (1666990080 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-5588385792 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (13231325184 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-22284337152 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (26528972800 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-21810380800 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (11777605632 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (-3758096384 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (536870912 : ℤ) 29 (by decide)]

theorem fixed_reversedU_typed_coeff_29 (n : ℕ) :
    fixedReversedUData_29.coeff n = fixedReversedUCoeff_29 n := by
  simp only [fixedReversedUData_29, fixedReversedUCoeff_29, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_29 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_29 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_29, ite_eq_right, add_zero]

def fixedReversedUData_30 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (480 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-38080 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (1188096 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-19348992 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (189190144 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-1203937280 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (5239111680 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-16066609152 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (35283533824 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-55710842880 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (62704844800 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-49073356800 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (25367150592 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-7784628224 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (1073741824 : ℤ)

def fixedReversedUCoeff_30 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (480 : ℤ) else 0) +
    (if 58 = n then (-38080 : ℤ) else 0) +
    (if 56 = n then (1188096 : ℤ) else 0) +
    (if 54 = n then (-19348992 : ℤ) else 0) +
    (if 52 = n then (189190144 : ℤ) else 0) +
    (if 50 = n then (-1203937280 : ℤ) else 0) +
    (if 48 = n then (5239111680 : ℤ) else 0) +
    (if 46 = n then (-16066609152 : ℤ) else 0) +
    (if 44 = n then (35283533824 : ℤ) else 0) +
    (if 42 = n then (-55710842880 : ℤ) else 0) +
    (if 40 = n then (62704844800 : ℤ) else 0) +
    (if 38 = n then (-49073356800 : ℤ) else 0) +
    (if 36 = n then (25367150592 : ℤ) else 0) +
    (if 34 = n then (-7784628224 : ℤ) else 0) +
    (if 32 = n then (1073741824 : ℤ) else 0)

theorem fixed_reversedU_typed_data_30 : reversedRow 63 fixedChebyshevUData_30 = fixedReversedUData_30 := by
  simp only [fixedChebyshevUData_30, fixedReversedUData_30, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (480 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-38080 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (1188096 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-19348992 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (189190144 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-1203937280 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (5239111680 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-16066609152 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (35283533824 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-55710842880 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (62704844800 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-49073356800 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (25367150592 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (-7784628224 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (1073741824 : ℤ) 30 (by decide)]

theorem fixed_reversedU_typed_coeff_30 (n : ℕ) :
    fixedReversedUData_30.coeff n = fixedReversedUCoeff_30 n := by
  simp only [fixedReversedUData_30, fixedReversedUCoeff_30, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_30 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_30 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_30, ite_eq_right, add_zero]

def fixedReversedUData_31 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-32 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (5440 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-274176 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (6449664 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-85995520 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (722362368 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-4074864640 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (16066609152 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-45364543488 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (92851404800 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-137950658560 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (147220070400 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-109924319232 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (54492397568 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-16106127360 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (2147483648 : ℤ)

def fixedReversedUCoeff_31 (n : ℕ) : ℤ :=
    (if 61 = n then (-32 : ℤ) else 0) +
    (if 59 = n then (5440 : ℤ) else 0) +
    (if 57 = n then (-274176 : ℤ) else 0) +
    (if 55 = n then (6449664 : ℤ) else 0) +
    (if 53 = n then (-85995520 : ℤ) else 0) +
    (if 51 = n then (722362368 : ℤ) else 0) +
    (if 49 = n then (-4074864640 : ℤ) else 0) +
    (if 47 = n then (16066609152 : ℤ) else 0) +
    (if 45 = n then (-45364543488 : ℤ) else 0) +
    (if 43 = n then (92851404800 : ℤ) else 0) +
    (if 41 = n then (-137950658560 : ℤ) else 0) +
    (if 39 = n then (147220070400 : ℤ) else 0) +
    (if 37 = n then (-109924319232 : ℤ) else 0) +
    (if 35 = n then (54492397568 : ℤ) else 0) +
    (if 33 = n then (-16106127360 : ℤ) else 0) +
    (if 31 = n then (2147483648 : ℤ) else 0)

theorem fixed_reversedU_typed_data_31 : reversedRow 63 fixedChebyshevUData_31 = fixedReversedUData_31 := by
  simp only [fixedChebyshevUData_31, fixedReversedUData_31, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-32 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (5440 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-274176 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (6449664 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-85995520 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (722362368 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-4074864640 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (16066609152 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-45364543488 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (92851404800 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-137950658560 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (147220070400 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-109924319232 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (54492397568 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (-16106127360 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (2147483648 : ℤ) 31 (by decide)]

theorem fixed_reversedU_typed_coeff_31 (n : ℕ) :
    fixedReversedUData_31.coeff n = fixedReversedUCoeff_31 n := by
  simp only [fixedReversedUData_31, fixedReversedUCoeff_31, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_31 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_31 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_31, ite_eq_right, add_zero]

end InternalCatalan

end

end

end OAI
