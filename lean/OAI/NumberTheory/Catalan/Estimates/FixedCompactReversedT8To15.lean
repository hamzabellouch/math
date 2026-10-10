import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedTData_8 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-32 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (160 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-256 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (128 : ℤ)

def fixedReversedTCoeff_8 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-32 : ℤ) else 0) +
    (if 58 = n then (160 : ℤ) else 0) +
    (if 56 = n then (-256 : ℤ) else 0) +
    (if 54 = n then (128 : ℤ) else 0)

theorem fixed_reversedT_typed_data_8 : reversedRow 63 fixedChebyshevTData_8 = fixedReversedTData_8 := by
  simp only [fixedChebyshevTData_8, fixedReversedTData_8, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-32 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (160 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-256 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (128 : ℤ) 8 (by decide)]

theorem fixed_reversedT_typed_coeff_8 (n : ℕ) :
    fixedReversedTData_8.coeff n = fixedReversedTCoeff_8 n := by
  simp only [fixedReversedTData_8, fixedReversedTCoeff_8, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_8 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_8 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_8, ite_eq_right, add_zero]

def fixedReversedTData_9 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (9 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-120 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (432 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-576 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (256 : ℤ)

def fixedReversedTCoeff_9 (n : ℕ) : ℤ :=
    (if 61 = n then (9 : ℤ) else 0) +
    (if 59 = n then (-120 : ℤ) else 0) +
    (if 57 = n then (432 : ℤ) else 0) +
    (if 55 = n then (-576 : ℤ) else 0) +
    (if 53 = n then (256 : ℤ) else 0)

theorem fixed_reversedT_typed_data_9 : reversedRow 63 fixedChebyshevTData_9 = fixedReversedTData_9 := by
  simp only [fixedChebyshevTData_9, fixedReversedTData_9, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (9 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-120 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (432 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-576 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (256 : ℤ) 9 (by decide)]

theorem fixed_reversedT_typed_coeff_9 (n : ℕ) :
    fixedReversedTData_9.coeff n = fixedReversedTCoeff_9 n := by
  simp only [fixedReversedTData_9, fixedReversedTCoeff_9, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_9 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_9 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_9, ite_eq_right, add_zero]

def fixedReversedTData_10 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (50 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-400 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (1120 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-1280 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (512 : ℤ)

def fixedReversedTCoeff_10 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (50 : ℤ) else 0) +
    (if 58 = n then (-400 : ℤ) else 0) +
    (if 56 = n then (1120 : ℤ) else 0) +
    (if 54 = n then (-1280 : ℤ) else 0) +
    (if 52 = n then (512 : ℤ) else 0)

theorem fixed_reversedT_typed_data_10 : reversedRow 63 fixedChebyshevTData_10 = fixedReversedTData_10 := by
  simp only [fixedChebyshevTData_10, fixedReversedTData_10, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (50 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-400 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (1120 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-1280 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (512 : ℤ) 10 (by decide)]

theorem fixed_reversedT_typed_coeff_10 (n : ℕ) :
    fixedReversedTData_10.coeff n = fixedReversedTCoeff_10 n := by
  simp only [fixedReversedTData_10, fixedReversedTCoeff_10, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_10 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_10 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_10, ite_eq_right, add_zero]

def fixedReversedTData_11 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-11 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (220 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-1232 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (2816 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-2816 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (1024 : ℤ)

def fixedReversedTCoeff_11 (n : ℕ) : ℤ :=
    (if 61 = n then (-11 : ℤ) else 0) +
    (if 59 = n then (220 : ℤ) else 0) +
    (if 57 = n then (-1232 : ℤ) else 0) +
    (if 55 = n then (2816 : ℤ) else 0) +
    (if 53 = n then (-2816 : ℤ) else 0) +
    (if 51 = n then (1024 : ℤ) else 0)

theorem fixed_reversedT_typed_data_11 : reversedRow 63 fixedChebyshevTData_11 = fixedReversedTData_11 := by
  simp only [fixedChebyshevTData_11, fixedReversedTData_11, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-11 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (220 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-1232 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (2816 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-2816 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (1024 : ℤ) 11 (by decide)]

theorem fixed_reversedT_typed_coeff_11 (n : ℕ) :
    fixedReversedTData_11.coeff n = fixedReversedTCoeff_11 n := by
  simp only [fixedReversedTData_11, fixedReversedTCoeff_11, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_11 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_11 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_11, ite_eq_right, add_zero]

def fixedReversedTData_12 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-72 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (840 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-3584 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (6912 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-6144 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (2048 : ℤ)

def fixedReversedTCoeff_12 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-72 : ℤ) else 0) +
    (if 58 = n then (840 : ℤ) else 0) +
    (if 56 = n then (-3584 : ℤ) else 0) +
    (if 54 = n then (6912 : ℤ) else 0) +
    (if 52 = n then (-6144 : ℤ) else 0) +
    (if 50 = n then (2048 : ℤ) else 0)

theorem fixed_reversedT_typed_data_12 : reversedRow 63 fixedChebyshevTData_12 = fixedReversedTData_12 := by
  simp only [fixedChebyshevTData_12, fixedReversedTData_12, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-72 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (840 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-3584 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (6912 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-6144 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (2048 : ℤ) 12 (by decide)]

theorem fixed_reversedT_typed_coeff_12 (n : ℕ) :
    fixedReversedTData_12.coeff n = fixedReversedTCoeff_12 n := by
  simp only [fixedReversedTData_12, fixedReversedTCoeff_12, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_12 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_12 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_12, ite_eq_right, add_zero]

def fixedReversedTData_13 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (13 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-364 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (2912 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-9984 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (16640 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-13312 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (4096 : ℤ)

def fixedReversedTCoeff_13 (n : ℕ) : ℤ :=
    (if 61 = n then (13 : ℤ) else 0) +
    (if 59 = n then (-364 : ℤ) else 0) +
    (if 57 = n then (2912 : ℤ) else 0) +
    (if 55 = n then (-9984 : ℤ) else 0) +
    (if 53 = n then (16640 : ℤ) else 0) +
    (if 51 = n then (-13312 : ℤ) else 0) +
    (if 49 = n then (4096 : ℤ) else 0)

theorem fixed_reversedT_typed_data_13 : reversedRow 63 fixedChebyshevTData_13 = fixedReversedTData_13 := by
  simp only [fixedChebyshevTData_13, fixedReversedTData_13, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (13 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-364 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (2912 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-9984 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (16640 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-13312 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (4096 : ℤ) 13 (by decide)]

theorem fixed_reversedT_typed_coeff_13 (n : ℕ) :
    fixedReversedTData_13.coeff n = fixedReversedTCoeff_13 n := by
  simp only [fixedReversedTData_13, fixedReversedTCoeff_13, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_13 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_13 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_13, ite_eq_right, add_zero]

def fixedReversedTData_14 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (98 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-1568 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (9408 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-26880 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (39424 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-28672 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (8192 : ℤ)

def fixedReversedTCoeff_14 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (98 : ℤ) else 0) +
    (if 58 = n then (-1568 : ℤ) else 0) +
    (if 56 = n then (9408 : ℤ) else 0) +
    (if 54 = n then (-26880 : ℤ) else 0) +
    (if 52 = n then (39424 : ℤ) else 0) +
    (if 50 = n then (-28672 : ℤ) else 0) +
    (if 48 = n then (8192 : ℤ) else 0)

theorem fixed_reversedT_typed_data_14 : reversedRow 63 fixedChebyshevTData_14 = fixedReversedTData_14 := by
  simp only [fixedChebyshevTData_14, fixedReversedTData_14, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (98 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-1568 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (9408 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-26880 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (39424 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-28672 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (8192 : ℤ) 14 (by decide)]

theorem fixed_reversedT_typed_coeff_14 (n : ℕ) :
    fixedReversedTData_14.coeff n = fixedReversedTCoeff_14 n := by
  simp only [fixedReversedTData_14, fixedReversedTCoeff_14, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_14 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_14 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_14, ite_eq_right, add_zero]

def fixedReversedTData_15 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-15 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (560 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-6048 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (28800 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-70400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (92160 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-61440 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (16384 : ℤ)

def fixedReversedTCoeff_15 (n : ℕ) : ℤ :=
    (if 61 = n then (-15 : ℤ) else 0) +
    (if 59 = n then (560 : ℤ) else 0) +
    (if 57 = n then (-6048 : ℤ) else 0) +
    (if 55 = n then (28800 : ℤ) else 0) +
    (if 53 = n then (-70400 : ℤ) else 0) +
    (if 51 = n then (92160 : ℤ) else 0) +
    (if 49 = n then (-61440 : ℤ) else 0) +
    (if 47 = n then (16384 : ℤ) else 0)

theorem fixed_reversedT_typed_data_15 : reversedRow 63 fixedChebyshevTData_15 = fixedReversedTData_15 := by
  simp only [fixedChebyshevTData_15, fixedReversedTData_15, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-15 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (560 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-6048 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (28800 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-70400 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (92160 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-61440 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (16384 : ℤ) 15 (by decide)]

theorem fixed_reversedT_typed_coeff_15 (n : ℕ) :
    fixedReversedTData_15.coeff n = fixedReversedTCoeff_15 n := by
  simp only [fixedReversedTData_15, fixedReversedTCoeff_15, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_15 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_15 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_15, ite_eq_right, add_zero]

end InternalCatalan

end

end

end OAI
