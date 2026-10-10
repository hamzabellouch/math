import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT0To7

namespace OAI

section

noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedUData_32 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-544 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (48960 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-1736448 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (32248320 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-361181184 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (2648662016 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-13388840960 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (48199827456 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-126012620800 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (241413652480 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-338606161920 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (343513497600 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-245215789056 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (116769423360 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-33285996544 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (4294967296 : ℤ)

def fixedReversedUCoeff_32 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-544 : ℤ) else 0) +
    (if 58 = n then (48960 : ℤ) else 0) +
    (if 56 = n then (-1736448 : ℤ) else 0) +
    (if 54 = n then (32248320 : ℤ) else 0) +
    (if 52 = n then (-361181184 : ℤ) else 0) +
    (if 50 = n then (2648662016 : ℤ) else 0) +
    (if 48 = n then (-13388840960 : ℤ) else 0) +
    (if 46 = n then (48199827456 : ℤ) else 0) +
    (if 44 = n then (-126012620800 : ℤ) else 0) +
    (if 42 = n then (241413652480 : ℤ) else 0) +
    (if 40 = n then (-338606161920 : ℤ) else 0) +
    (if 38 = n then (343513497600 : ℤ) else 0) +
    (if 36 = n then (-245215789056 : ℤ) else 0) +
    (if 34 = n then (116769423360 : ℤ) else 0) +
    (if 32 = n then (-33285996544 : ℤ) else 0) +
    (if 30 = n then (4294967296 : ℤ) else 0)

theorem fixed_reversedU_typed_data_32 : reversedRow 63 fixedChebyshevUData_32 = fixedReversedUData_32 := by
  simp only [fixedChebyshevUData_32, fixedReversedUData_32, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-544 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (48960 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-1736448 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (32248320 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-361181184 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (2648662016 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-13388840960 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (48199827456 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-126012620800 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (241413652480 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-338606161920 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (343513497600 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-245215789056 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (116769423360 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (-33285996544 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (4294967296 : ℤ) 32 (by decide)]

theorem fixed_reversedU_typed_coeff_32 (n : ℕ) :
    fixedReversedUData_32.coeff n = fixedReversedUCoeff_32 n := by
  simp only [fixedReversedUData_32, fixedReversedUCoeff_32, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_32 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_32 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_32, ite_eq_right, add_zero]

def fixedReversedUData_33 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (34 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-6528 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (372096 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-9922560 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (150492160 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-1444724736 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (9372188672 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-42844291072 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (141764198400 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-344876646400 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (620777963520 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-824432394240 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (796951314432 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-544923975680 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (249644974080 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-68719476736 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (8589934592 : ℤ)

def fixedReversedUCoeff_33 (n : ℕ) : ℤ :=
    (if 61 = n then (34 : ℤ) else 0) +
    (if 59 = n then (-6528 : ℤ) else 0) +
    (if 57 = n then (372096 : ℤ) else 0) +
    (if 55 = n then (-9922560 : ℤ) else 0) +
    (if 53 = n then (150492160 : ℤ) else 0) +
    (if 51 = n then (-1444724736 : ℤ) else 0) +
    (if 49 = n then (9372188672 : ℤ) else 0) +
    (if 47 = n then (-42844291072 : ℤ) else 0) +
    (if 45 = n then (141764198400 : ℤ) else 0) +
    (if 43 = n then (-344876646400 : ℤ) else 0) +
    (if 41 = n then (620777963520 : ℤ) else 0) +
    (if 39 = n then (-824432394240 : ℤ) else 0) +
    (if 37 = n then (796951314432 : ℤ) else 0) +
    (if 35 = n then (-544923975680 : ℤ) else 0) +
    (if 33 = n then (249644974080 : ℤ) else 0) +
    (if 31 = n then (-68719476736 : ℤ) else 0) +
    (if 29 = n then (8589934592 : ℤ) else 0)

theorem fixed_reversedU_typed_data_33 : reversedRow 63 fixedChebyshevUData_33 = fixedReversedUData_33 := by
  simp only [fixedChebyshevUData_33, fixedReversedUData_33, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (34 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-6528 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (372096 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-9922560 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (150492160 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-1444724736 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (9372188672 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-42844291072 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (141764198400 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-344876646400 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (620777963520 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-824432394240 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (796951314432 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (-544923975680 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (249644974080 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (-68719476736 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (8589934592 : ℤ) 33 (by decide)]

theorem fixed_reversedU_typed_coeff_33 (n : ℕ) :
    fixedReversedUData_33.coeff n = fixedReversedUCoeff_33 n := by
  simp only [fixedReversedUData_33, fixedReversedUCoeff_33, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_33 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_33 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_33, ite_eq_right, add_zero]

def fixedReversedUData_34 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (612 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-62016 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (2480640 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-52093440 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (662165504 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-5538111488 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (32133218304 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-133888409600 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (409541017600 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-931166945280 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (1580162088960 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-1992378286080 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (1839118417920 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-1206617374720 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (532575944704 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-141733920768 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (17179869184 : ℤ)

def fixedReversedUCoeff_34 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (612 : ℤ) else 0) +
    (if 58 = n then (-62016 : ℤ) else 0) +
    (if 56 = n then (2480640 : ℤ) else 0) +
    (if 54 = n then (-52093440 : ℤ) else 0) +
    (if 52 = n then (662165504 : ℤ) else 0) +
    (if 50 = n then (-5538111488 : ℤ) else 0) +
    (if 48 = n then (32133218304 : ℤ) else 0) +
    (if 46 = n then (-133888409600 : ℤ) else 0) +
    (if 44 = n then (409541017600 : ℤ) else 0) +
    (if 42 = n then (-931166945280 : ℤ) else 0) +
    (if 40 = n then (1580162088960 : ℤ) else 0) +
    (if 38 = n then (-1992378286080 : ℤ) else 0) +
    (if 36 = n then (1839118417920 : ℤ) else 0) +
    (if 34 = n then (-1206617374720 : ℤ) else 0) +
    (if 32 = n then (532575944704 : ℤ) else 0) +
    (if 30 = n then (-141733920768 : ℤ) else 0) +
    (if 28 = n then (17179869184 : ℤ) else 0)

theorem fixed_reversedU_typed_data_34 : reversedRow 63 fixedChebyshevUData_34 = fixedReversedUData_34 := by
  simp only [fixedChebyshevUData_34, fixedReversedUData_34, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (612 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-62016 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (2480640 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-52093440 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (662165504 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-5538111488 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (32133218304 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-133888409600 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (409541017600 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-931166945280 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (1580162088960 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-1992378286080 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (1839118417920 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (-1206617374720 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (532575944704 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (-141733920768 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (17179869184 : ℤ) 34 (by decide)]

theorem fixed_reversedU_typed_coeff_34 (n : ℕ) :
    fixedReversedUData_34.coeff n = fixedReversedUCoeff_34 n := by
  simp only [fixedReversedUData_34, fixedReversedUCoeff_34, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_34 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_34 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_34, ite_eq_right, add_zero]

def fixedReversedUData_35 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-36 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (7752 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-496128 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (14883840 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-254679040 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (2769055744 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-20448411648 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (107110727680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-409541017600 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (1163958681600 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-2483111854080 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (3984756572160 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-4781707886592 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (4223160811520 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-2662879723520 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (1133871366144 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-292057776128 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (34359738368 : ℤ)

def fixedReversedUCoeff_35 (n : ℕ) : ℤ :=
    (if 61 = n then (-36 : ℤ) else 0) +
    (if 59 = n then (7752 : ℤ) else 0) +
    (if 57 = n then (-496128 : ℤ) else 0) +
    (if 55 = n then (14883840 : ℤ) else 0) +
    (if 53 = n then (-254679040 : ℤ) else 0) +
    (if 51 = n then (2769055744 : ℤ) else 0) +
    (if 49 = n then (-20448411648 : ℤ) else 0) +
    (if 47 = n then (107110727680 : ℤ) else 0) +
    (if 45 = n then (-409541017600 : ℤ) else 0) +
    (if 43 = n then (1163958681600 : ℤ) else 0) +
    (if 41 = n then (-2483111854080 : ℤ) else 0) +
    (if 39 = n then (3984756572160 : ℤ) else 0) +
    (if 37 = n then (-4781707886592 : ℤ) else 0) +
    (if 35 = n then (4223160811520 : ℤ) else 0) +
    (if 33 = n then (-2662879723520 : ℤ) else 0) +
    (if 31 = n then (1133871366144 : ℤ) else 0) +
    (if 29 = n then (-292057776128 : ℤ) else 0) +
    (if 27 = n then (34359738368 : ℤ) else 0)

theorem fixed_reversedU_typed_data_35 : reversedRow 63 fixedChebyshevUData_35 = fixedReversedUData_35 := by
  simp only [fixedChebyshevUData_35, fixedReversedUData_35, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-36 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (7752 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-496128 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (14883840 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-254679040 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (2769055744 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-20448411648 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (107110727680 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-409541017600 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (1163958681600 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-2483111854080 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (3984756572160 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-4781707886592 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (4223160811520 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (-2662879723520 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (1133871366144 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (-292057776128 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (34359738368 : ℤ) 35 (by decide)]

theorem fixed_reversedU_typed_coeff_35 (n : ℕ) :
    fixedReversedUData_35.coeff n = fixedReversedUCoeff_35 n := by
  simp only [fixedReversedUData_35, fixedReversedUCoeff_35, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_35 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_35 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_35, ite_eq_right, add_zero]

def fixedReversedUData_36 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-684 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (77520 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-3472896 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (81861120 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-1171523584 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (11076222976 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-73030041600 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (348109864960 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-1228623052800 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (3259084308480 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-6546385797120 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (9961891430400 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-11402534191104 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (9652938997760 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-5858335391744 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (2409476653056 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-601295421440 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (68719476736 : ℤ)

def fixedReversedUCoeff_36 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-684 : ℤ) else 0) +
    (if 58 = n then (77520 : ℤ) else 0) +
    (if 56 = n then (-3472896 : ℤ) else 0) +
    (if 54 = n then (81861120 : ℤ) else 0) +
    (if 52 = n then (-1171523584 : ℤ) else 0) +
    (if 50 = n then (11076222976 : ℤ) else 0) +
    (if 48 = n then (-73030041600 : ℤ) else 0) +
    (if 46 = n then (348109864960 : ℤ) else 0) +
    (if 44 = n then (-1228623052800 : ℤ) else 0) +
    (if 42 = n then (3259084308480 : ℤ) else 0) +
    (if 40 = n then (-6546385797120 : ℤ) else 0) +
    (if 38 = n then (9961891430400 : ℤ) else 0) +
    (if 36 = n then (-11402534191104 : ℤ) else 0) +
    (if 34 = n then (9652938997760 : ℤ) else 0) +
    (if 32 = n then (-5858335391744 : ℤ) else 0) +
    (if 30 = n then (2409476653056 : ℤ) else 0) +
    (if 28 = n then (-601295421440 : ℤ) else 0) +
    (if 26 = n then (68719476736 : ℤ) else 0)

theorem fixed_reversedU_typed_data_36 : reversedRow 63 fixedChebyshevUData_36 = fixedReversedUData_36 := by
  simp only [fixedChebyshevUData_36, fixedReversedUData_36, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-684 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (77520 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-3472896 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (81861120 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-1171523584 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (11076222976 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-73030041600 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (348109864960 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-1228623052800 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (3259084308480 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-6546385797120 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (9961891430400 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-11402534191104 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (9652938997760 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (-5858335391744 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (2409476653056 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (-601295421440 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (68719476736 : ℤ) 36 (by decide)]

theorem fixed_reversedU_typed_coeff_36 (n : ℕ) :
    fixedReversedUData_36.coeff n = fixedReversedUCoeff_36 n := by
  simp only [fixedReversedUData_36, fixedReversedUCoeff_36, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_36 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_36 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_36, ite_eq_right, add_zero]

def fixedReversedUData_37 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (38 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-9120 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (651168 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-21829632 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (418401280 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-5112102912 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (42600857600 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-253170810880 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (1105760747520 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-3621204787200 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (9001280471040 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-17077528166400 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (24705490747392 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-27028229193728 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (21968757719040 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-12850542149632 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (5111011082240 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-1236950581248 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (137438953472 : ℤ)

def fixedReversedUCoeff_37 (n : ℕ) : ℤ :=
    (if 61 = n then (38 : ℤ) else 0) +
    (if 59 = n then (-9120 : ℤ) else 0) +
    (if 57 = n then (651168 : ℤ) else 0) +
    (if 55 = n then (-21829632 : ℤ) else 0) +
    (if 53 = n then (418401280 : ℤ) else 0) +
    (if 51 = n then (-5112102912 : ℤ) else 0) +
    (if 49 = n then (42600857600 : ℤ) else 0) +
    (if 47 = n then (-253170810880 : ℤ) else 0) +
    (if 45 = n then (1105760747520 : ℤ) else 0) +
    (if 43 = n then (-3621204787200 : ℤ) else 0) +
    (if 41 = n then (9001280471040 : ℤ) else 0) +
    (if 39 = n then (-17077528166400 : ℤ) else 0) +
    (if 37 = n then (24705490747392 : ℤ) else 0) +
    (if 35 = n then (-27028229193728 : ℤ) else 0) +
    (if 33 = n then (21968757719040 : ℤ) else 0) +
    (if 31 = n then (-12850542149632 : ℤ) else 0) +
    (if 29 = n then (5111011082240 : ℤ) else 0) +
    (if 27 = n then (-1236950581248 : ℤ) else 0) +
    (if 25 = n then (137438953472 : ℤ) else 0)

theorem fixed_reversedU_typed_data_37 : reversedRow 63 fixedChebyshevUData_37 = fixedReversedUData_37 := by
  simp only [fixedChebyshevUData_37, fixedReversedUData_37, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (38 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-9120 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (651168 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-21829632 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (418401280 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-5112102912 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (42600857600 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-253170810880 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (1105760747520 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-3621204787200 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (9001280471040 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-17077528166400 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (24705490747392 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (-27028229193728 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (21968757719040 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (-12850542149632 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (5111011082240 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (-1236950581248 : ℤ) 35 (by decide),
    fixedTyped_reversedRow_monomial (137438953472 : ℤ) 37 (by decide)]

theorem fixed_reversedU_typed_coeff_37 (n : ℕ) :
    fixedReversedUData_37.coeff n = fixedReversedUCoeff_37 n := by
  simp only [fixedReversedUData_37, fixedReversedUCoeff_37, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_37 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_37 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_37, ite_eq_right, add_zero]

def fixedReversedUData_38 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (760 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-95760 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (4775232 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-125520384 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (2008326144 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-21300428800 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (158231756800 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-854451486720 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (3440144547840 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-10501493882880 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (24548946739200 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-44116947763200 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (60813515685888 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-63709397385216 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (49795850829824 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-28110560952320 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (10823317585920 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-2542620639232 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (274877906944 : ℤ)

def fixedReversedUCoeff_38 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (760 : ℤ) else 0) +
    (if 58 = n then (-95760 : ℤ) else 0) +
    (if 56 = n then (4775232 : ℤ) else 0) +
    (if 54 = n then (-125520384 : ℤ) else 0) +
    (if 52 = n then (2008326144 : ℤ) else 0) +
    (if 50 = n then (-21300428800 : ℤ) else 0) +
    (if 48 = n then (158231756800 : ℤ) else 0) +
    (if 46 = n then (-854451486720 : ℤ) else 0) +
    (if 44 = n then (3440144547840 : ℤ) else 0) +
    (if 42 = n then (-10501493882880 : ℤ) else 0) +
    (if 40 = n then (24548946739200 : ℤ) else 0) +
    (if 38 = n then (-44116947763200 : ℤ) else 0) +
    (if 36 = n then (60813515685888 : ℤ) else 0) +
    (if 34 = n then (-63709397385216 : ℤ) else 0) +
    (if 32 = n then (49795850829824 : ℤ) else 0) +
    (if 30 = n then (-28110560952320 : ℤ) else 0) +
    (if 28 = n then (10823317585920 : ℤ) else 0) +
    (if 26 = n then (-2542620639232 : ℤ) else 0) +
    (if 24 = n then (274877906944 : ℤ) else 0)

theorem fixed_reversedU_typed_data_38 : reversedRow 63 fixedChebyshevUData_38 = fixedReversedUData_38 := by
  simp only [fixedChebyshevUData_38, fixedReversedUData_38, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (760 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-95760 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (4775232 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-125520384 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (2008326144 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-21300428800 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (158231756800 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-854451486720 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (3440144547840 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-10501493882880 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (24548946739200 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-44116947763200 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (60813515685888 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (-63709397385216 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (49795850829824 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (-28110560952320 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (10823317585920 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (-2542620639232 : ℤ) 36 (by decide),
    fixedTyped_reversedRow_monomial (274877906944 : ℤ) 38 (by decide)]

theorem fixed_reversedU_typed_coeff_38 (n : ℕ) :
    fixedReversedUData_38.coeff n = fixedReversedUCoeff_38 n := by
  simp only [fixedReversedUData_38, fixedReversedUCoeff_38, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_38 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_38 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_38, ite_eq_right, add_zero]

def fixedReversedUData_39 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-40 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (10640 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-842688 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (31380096 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-669442048 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (9128755200 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-85201715200 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (569634324480 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-2814663720960 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (10501493882880 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-30004268236800 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (66175421644800 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-112939386273792 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (148655260565504 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-149387552489472 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (112442243809280 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-61332132986880 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (22883585753088 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-5222680231936 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (549755813888 : ℤ)

def fixedReversedUCoeff_39 (n : ℕ) : ℤ :=
    (if 61 = n then (-40 : ℤ) else 0) +
    (if 59 = n then (10640 : ℤ) else 0) +
    (if 57 = n then (-842688 : ℤ) else 0) +
    (if 55 = n then (31380096 : ℤ) else 0) +
    (if 53 = n then (-669442048 : ℤ) else 0) +
    (if 51 = n then (9128755200 : ℤ) else 0) +
    (if 49 = n then (-85201715200 : ℤ) else 0) +
    (if 47 = n then (569634324480 : ℤ) else 0) +
    (if 45 = n then (-2814663720960 : ℤ) else 0) +
    (if 43 = n then (10501493882880 : ℤ) else 0) +
    (if 41 = n then (-30004268236800 : ℤ) else 0) +
    (if 39 = n then (66175421644800 : ℤ) else 0) +
    (if 37 = n then (-112939386273792 : ℤ) else 0) +
    (if 35 = n then (148655260565504 : ℤ) else 0) +
    (if 33 = n then (-149387552489472 : ℤ) else 0) +
    (if 31 = n then (112442243809280 : ℤ) else 0) +
    (if 29 = n then (-61332132986880 : ℤ) else 0) +
    (if 27 = n then (22883585753088 : ℤ) else 0) +
    (if 25 = n then (-5222680231936 : ℤ) else 0) +
    (if 23 = n then (549755813888 : ℤ) else 0)

theorem fixed_reversedU_typed_data_39 : reversedRow 63 fixedChebyshevUData_39 = fixedReversedUData_39 := by
  simp only [fixedChebyshevUData_39, fixedReversedUData_39, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-40 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (10640 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-842688 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (31380096 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-669442048 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (9128755200 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-85201715200 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (569634324480 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-2814663720960 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (10501493882880 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-30004268236800 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (66175421644800 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-112939386273792 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (148655260565504 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (-149387552489472 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (112442243809280 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (-61332132986880 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (22883585753088 : ℤ) 35 (by decide),
    fixedTyped_reversedRow_monomial (-5222680231936 : ℤ) 37 (by decide),
    fixedTyped_reversedRow_monomial (549755813888 : ℤ) 39 (by decide)]

theorem fixed_reversedU_typed_coeff_39 (n : ℕ) :
    fixedReversedUData_39.coeff n = fixedReversedUCoeff_39 n := by
  simp only [fixedReversedUData_39, fixedReversedUCoeff_39, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_39 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_39 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_39, ite_eq_right, add_zero]

end InternalCatalan

end

end

end OAI
