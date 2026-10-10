import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedUData_8 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-40 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (240 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-448 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (256 : ℤ)

def fixedReversedUCoeff_8 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-40 : ℤ) else 0) +
    (if 58 = n then (240 : ℤ) else 0) +
    (if 56 = n then (-448 : ℤ) else 0) +
    (if 54 = n then (256 : ℤ) else 0)

theorem fixed_reversedU_typed_data_8 : reversedRow 63 fixedChebyshevUData_8 = fixedReversedUData_8 := by
  simp only [fixedChebyshevUData_8, fixedReversedUData_8, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-40 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (240 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-448 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (256 : ℤ) 8 (by decide)]

theorem fixed_reversedU_typed_coeff_8 (n : ℕ) :
    fixedReversedUData_8.coeff n = fixedReversedUCoeff_8 n := by
  simp only [fixedReversedUData_8, fixedReversedUCoeff_8, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_8 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_8 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_8, ite_eq_right, add_zero]

def fixedReversedUData_9 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (10 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-160 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (672 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-1024 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (512 : ℤ)

def fixedReversedUCoeff_9 (n : ℕ) : ℤ :=
    (if 61 = n then (10 : ℤ) else 0) +
    (if 59 = n then (-160 : ℤ) else 0) +
    (if 57 = n then (672 : ℤ) else 0) +
    (if 55 = n then (-1024 : ℤ) else 0) +
    (if 53 = n then (512 : ℤ) else 0)

theorem fixed_reversedU_typed_data_9 : reversedRow 63 fixedChebyshevUData_9 = fixedReversedUData_9 := by
  simp only [fixedChebyshevUData_9, fixedReversedUData_9, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (10 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-160 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (672 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-1024 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (512 : ℤ) 9 (by decide)]

theorem fixed_reversedU_typed_coeff_9 (n : ℕ) :
    fixedReversedUData_9.coeff n = fixedReversedUCoeff_9 n := by
  simp only [fixedReversedUData_9, fixedReversedUCoeff_9, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_9 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_9 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_9, ite_eq_right, add_zero]

def fixedReversedUData_10 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (60 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-560 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (1792 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-2304 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (1024 : ℤ)

def fixedReversedUCoeff_10 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (60 : ℤ) else 0) +
    (if 58 = n then (-560 : ℤ) else 0) +
    (if 56 = n then (1792 : ℤ) else 0) +
    (if 54 = n then (-2304 : ℤ) else 0) +
    (if 52 = n then (1024 : ℤ) else 0)

theorem fixed_reversedU_typed_data_10 : reversedRow 63 fixedChebyshevUData_10 = fixedReversedUData_10 := by
  simp only [fixedChebyshevUData_10, fixedReversedUData_10, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (60 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-560 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (1792 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-2304 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (1024 : ℤ) 10 (by decide)]

theorem fixed_reversedU_typed_coeff_10 (n : ℕ) :
    fixedReversedUData_10.coeff n = fixedReversedUCoeff_10 n := by
  simp only [fixedReversedUData_10, fixedReversedUCoeff_10, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_10 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_10 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_10, ite_eq_right, add_zero]

def fixedReversedUData_11 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-12 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (280 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-1792 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (4608 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-5120 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (2048 : ℤ)

def fixedReversedUCoeff_11 (n : ℕ) : ℤ :=
    (if 61 = n then (-12 : ℤ) else 0) +
    (if 59 = n then (280 : ℤ) else 0) +
    (if 57 = n then (-1792 : ℤ) else 0) +
    (if 55 = n then (4608 : ℤ) else 0) +
    (if 53 = n then (-5120 : ℤ) else 0) +
    (if 51 = n then (2048 : ℤ) else 0)

theorem fixed_reversedU_typed_data_11 : reversedRow 63 fixedChebyshevUData_11 = fixedReversedUData_11 := by
  simp only [fixedChebyshevUData_11, fixedReversedUData_11, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-12 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (280 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-1792 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (4608 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-5120 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (2048 : ℤ) 11 (by decide)]

theorem fixed_reversedU_typed_coeff_11 (n : ℕ) :
    fixedReversedUData_11.coeff n = fixedReversedUCoeff_11 n := by
  simp only [fixedReversedUData_11, fixedReversedUCoeff_11, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_11 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_11 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_11, ite_eq_right, add_zero]

def fixedReversedUData_12 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-84 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (1120 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-5376 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (11520 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-11264 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (4096 : ℤ)

def fixedReversedUCoeff_12 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-84 : ℤ) else 0) +
    (if 58 = n then (1120 : ℤ) else 0) +
    (if 56 = n then (-5376 : ℤ) else 0) +
    (if 54 = n then (11520 : ℤ) else 0) +
    (if 52 = n then (-11264 : ℤ) else 0) +
    (if 50 = n then (4096 : ℤ) else 0)

theorem fixed_reversedU_typed_data_12 : reversedRow 63 fixedChebyshevUData_12 = fixedReversedUData_12 := by
  simp only [fixedChebyshevUData_12, fixedReversedUData_12, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-84 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (1120 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-5376 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (11520 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-11264 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (4096 : ℤ) 12 (by decide)]

theorem fixed_reversedU_typed_coeff_12 (n : ℕ) :
    fixedReversedUData_12.coeff n = fixedReversedUCoeff_12 n := by
  simp only [fixedReversedUData_12, fixedReversedUCoeff_12, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_12 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_12 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_12, ite_eq_right, add_zero]

def fixedReversedUData_13 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (14 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-448 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (4032 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-15360 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (28160 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-24576 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (8192 : ℤ)

def fixedReversedUCoeff_13 (n : ℕ) : ℤ :=
    (if 61 = n then (14 : ℤ) else 0) +
    (if 59 = n then (-448 : ℤ) else 0) +
    (if 57 = n then (4032 : ℤ) else 0) +
    (if 55 = n then (-15360 : ℤ) else 0) +
    (if 53 = n then (28160 : ℤ) else 0) +
    (if 51 = n then (-24576 : ℤ) else 0) +
    (if 49 = n then (8192 : ℤ) else 0)

theorem fixed_reversedU_typed_data_13 : reversedRow 63 fixedChebyshevUData_13 = fixedReversedUData_13 := by
  simp only [fixedChebyshevUData_13, fixedReversedUData_13, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (14 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-448 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (4032 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-15360 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (28160 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-24576 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (8192 : ℤ) 13 (by decide)]

theorem fixed_reversedU_typed_coeff_13 (n : ℕ) :
    fixedReversedUData_13.coeff n = fixedReversedUCoeff_13 n := by
  simp only [fixedReversedUData_13, fixedReversedUCoeff_13, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_13 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_13 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_13, ite_eq_right, add_zero]

def fixedReversedUData_14 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (112 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-2016 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (13440 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-42240 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (67584 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-53248 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (16384 : ℤ)

def fixedReversedUCoeff_14 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (112 : ℤ) else 0) +
    (if 58 = n then (-2016 : ℤ) else 0) +
    (if 56 = n then (13440 : ℤ) else 0) +
    (if 54 = n then (-42240 : ℤ) else 0) +
    (if 52 = n then (67584 : ℤ) else 0) +
    (if 50 = n then (-53248 : ℤ) else 0) +
    (if 48 = n then (16384 : ℤ) else 0)

theorem fixed_reversedU_typed_data_14 : reversedRow 63 fixedChebyshevUData_14 = fixedReversedUData_14 := by
  simp only [fixedChebyshevUData_14, fixedReversedUData_14, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (112 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-2016 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (13440 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-42240 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (67584 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-53248 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (16384 : ℤ) 14 (by decide)]

theorem fixed_reversedU_typed_coeff_14 (n : ℕ) :
    fixedReversedUData_14.coeff n = fixedReversedUCoeff_14 n := by
  simp only [fixedReversedUData_14, fixedReversedUCoeff_14, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_14 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_14 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_14, ite_eq_right, add_zero]

def fixedReversedUData_15 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-16 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (672 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-8064 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (42240 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-112640 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (159744 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-114688 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (32768 : ℤ)

def fixedReversedUCoeff_15 (n : ℕ) : ℤ :=
    (if 61 = n then (-16 : ℤ) else 0) +
    (if 59 = n then (672 : ℤ) else 0) +
    (if 57 = n then (-8064 : ℤ) else 0) +
    (if 55 = n then (42240 : ℤ) else 0) +
    (if 53 = n then (-112640 : ℤ) else 0) +
    (if 51 = n then (159744 : ℤ) else 0) +
    (if 49 = n then (-114688 : ℤ) else 0) +
    (if 47 = n then (32768 : ℤ) else 0)

theorem fixed_reversedU_typed_data_15 : reversedRow 63 fixedChebyshevUData_15 = fixedReversedUData_15 := by
  simp only [fixedChebyshevUData_15, fixedReversedUData_15, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-16 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (672 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-8064 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (42240 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-112640 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (159744 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-114688 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (32768 : ℤ) 15 (by decide)]

theorem fixed_reversedU_typed_coeff_15 (n : ℕ) :
    fixedReversedUData_15.coeff n = fixedReversedUCoeff_15 n := by
  simp only [fixedReversedUData_15, fixedReversedUCoeff_15, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_15 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_15 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_15, ite_eq_right, add_zero]

end InternalCatalan

end

end

end OAI
