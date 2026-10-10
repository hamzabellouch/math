import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedUData_0 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ)

def fixedReversedUCoeff_0 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0)

theorem fixed_reversedU_typed_data_0 : reversedRow 63 fixedChebyshevUData_0 = fixedReversedUData_0 := by
  simp only [fixedChebyshevUData_0, fixedReversedUData_0]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide)]

theorem fixed_reversedU_typed_coeff_0 (n : ℕ) :
    fixedReversedUData_0.coeff n = fixedReversedUCoeff_0 n := by
  simp only [fixedReversedUData_0, fixedReversedUCoeff_0, coeff_monomial]

theorem fixed_reversedU_typed_tail_0 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_0 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_0, ite_eq_right]

def fixedReversedUData_1 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (2 : ℤ)

def fixedReversedUCoeff_1 (n : ℕ) : ℤ :=
    (if 61 = n then (2 : ℤ) else 0)

theorem fixed_reversedU_typed_data_1 : reversedRow 63 fixedChebyshevUData_1 = fixedReversedUData_1 := by
  simp only [fixedChebyshevUData_1, fixedReversedUData_1]
  rw [fixedTyped_reversedRow_monomial (2 : ℤ) 1 (by decide)]

theorem fixed_reversedU_typed_coeff_1 (n : ℕ) :
    fixedReversedUData_1.coeff n = fixedReversedUCoeff_1 n := by
  simp only [fixedReversedUData_1, fixedReversedUCoeff_1, coeff_monomial]

theorem fixed_reversedU_typed_tail_1 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_1 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_1, ite_eq_right]

def fixedReversedUData_2 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (4 : ℤ)

def fixedReversedUCoeff_2 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (4 : ℤ) else 0)

theorem fixed_reversedU_typed_data_2 : reversedRow 63 fixedChebyshevUData_2 = fixedReversedUData_2 := by
  simp only [fixedChebyshevUData_2, fixedReversedUData_2, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (4 : ℤ) 2 (by decide)]

theorem fixed_reversedU_typed_coeff_2 (n : ℕ) :
    fixedReversedUData_2.coeff n = fixedReversedUCoeff_2 n := by
  simp only [fixedReversedUData_2, fixedReversedUCoeff_2, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_2 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_2 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_2, ite_eq_right, add_zero]

def fixedReversedUData_3 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-4 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (8 : ℤ)

def fixedReversedUCoeff_3 (n : ℕ) : ℤ :=
    (if 61 = n then (-4 : ℤ) else 0) +
    (if 59 = n then (8 : ℤ) else 0)

theorem fixed_reversedU_typed_data_3 : reversedRow 63 fixedChebyshevUData_3 = fixedReversedUData_3 := by
  simp only [fixedChebyshevUData_3, fixedReversedUData_3, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-4 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (8 : ℤ) 3 (by decide)]

theorem fixed_reversedU_typed_coeff_3 (n : ℕ) :
    fixedReversedUData_3.coeff n = fixedReversedUCoeff_3 n := by
  simp only [fixedReversedUData_3, fixedReversedUCoeff_3, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_3 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_3 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_3, ite_eq_right, add_zero]

def fixedReversedUData_4 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-12 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (16 : ℤ)

def fixedReversedUCoeff_4 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-12 : ℤ) else 0) +
    (if 58 = n then (16 : ℤ) else 0)

theorem fixed_reversedU_typed_data_4 : reversedRow 63 fixedChebyshevUData_4 = fixedReversedUData_4 := by
  simp only [fixedChebyshevUData_4, fixedReversedUData_4, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-12 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (16 : ℤ) 4 (by decide)]

theorem fixed_reversedU_typed_coeff_4 (n : ℕ) :
    fixedReversedUData_4.coeff n = fixedReversedUCoeff_4 n := by
  simp only [fixedReversedUData_4, fixedReversedUCoeff_4, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_4 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_4 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_4, ite_eq_right, add_zero]

def fixedReversedUData_5 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (6 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-32 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (32 : ℤ)

def fixedReversedUCoeff_5 (n : ℕ) : ℤ :=
    (if 61 = n then (6 : ℤ) else 0) +
    (if 59 = n then (-32 : ℤ) else 0) +
    (if 57 = n then (32 : ℤ) else 0)

theorem fixed_reversedU_typed_data_5 : reversedRow 63 fixedChebyshevUData_5 = fixedReversedUData_5 := by
  simp only [fixedChebyshevUData_5, fixedReversedUData_5, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (6 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-32 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (32 : ℤ) 5 (by decide)]

theorem fixed_reversedU_typed_coeff_5 (n : ℕ) :
    fixedReversedUData_5.coeff n = fixedReversedUCoeff_5 n := by
  simp only [fixedReversedUData_5, fixedReversedUCoeff_5, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_5 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_5 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_5, ite_eq_right, add_zero]

def fixedReversedUData_6 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (24 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-80 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (64 : ℤ)

def fixedReversedUCoeff_6 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (24 : ℤ) else 0) +
    (if 58 = n then (-80 : ℤ) else 0) +
    (if 56 = n then (64 : ℤ) else 0)

theorem fixed_reversedU_typed_data_6 : reversedRow 63 fixedChebyshevUData_6 = fixedReversedUData_6 := by
  simp only [fixedChebyshevUData_6, fixedReversedUData_6, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (24 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-80 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (64 : ℤ) 6 (by decide)]

theorem fixed_reversedU_typed_coeff_6 (n : ℕ) :
    fixedReversedUData_6.coeff n = fixedReversedUCoeff_6 n := by
  simp only [fixedReversedUData_6, fixedReversedUCoeff_6, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_6 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_6 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_6, ite_eq_right, add_zero]

def fixedReversedUData_7 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-8 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (80 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-192 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (128 : ℤ)

def fixedReversedUCoeff_7 (n : ℕ) : ℤ :=
    (if 61 = n then (-8 : ℤ) else 0) +
    (if 59 = n then (80 : ℤ) else 0) +
    (if 57 = n then (-192 : ℤ) else 0) +
    (if 55 = n then (128 : ℤ) else 0)

theorem fixed_reversedU_typed_data_7 : reversedRow 63 fixedChebyshevUData_7 = fixedReversedUData_7 := by
  simp only [fixedChebyshevUData_7, fixedReversedUData_7, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-8 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (80 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-192 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (128 : ℤ) 7 (by decide)]

theorem fixed_reversedU_typed_coeff_7 (n : ℕ) :
    fixedReversedUData_7.coeff n = fixedReversedUCoeff_7 n := by
  simp only [fixedReversedUData_7, fixedReversedUCoeff_7, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_7 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_7 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_7, ite_eq_right, add_zero]

end InternalCatalan

end

end

end OAI
