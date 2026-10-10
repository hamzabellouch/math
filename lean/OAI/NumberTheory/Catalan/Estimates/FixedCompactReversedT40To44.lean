import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT0To7

namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedTData_40 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-800 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (106400 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-5617920 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (156900480 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-2677768192 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (30429184000 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-243433472000 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (1424085811200 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-6254808268800 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (21002987765760 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-54553214976000 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (110292369408000 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-173752901959680 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (212364657950720 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-199183403319296 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (140552804761600 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-72155450572800 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (25426206392320 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-5497558138880 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (549755813888 : ℤ)

def fixedReversedTCoeff_40 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-800 : ℤ) else 0) +
    (if 58 = n then (106400 : ℤ) else 0) +
    (if 56 = n then (-5617920 : ℤ) else 0) +
    (if 54 = n then (156900480 : ℤ) else 0) +
    (if 52 = n then (-2677768192 : ℤ) else 0) +
    (if 50 = n then (30429184000 : ℤ) else 0) +
    (if 48 = n then (-243433472000 : ℤ) else 0) +
    (if 46 = n then (1424085811200 : ℤ) else 0) +
    (if 44 = n then (-6254808268800 : ℤ) else 0) +
    (if 42 = n then (21002987765760 : ℤ) else 0) +
    (if 40 = n then (-54553214976000 : ℤ) else 0) +
    (if 38 = n then (110292369408000 : ℤ) else 0) +
    (if 36 = n then (-173752901959680 : ℤ) else 0) +
    (if 34 = n then (212364657950720 : ℤ) else 0) +
    (if 32 = n then (-199183403319296 : ℤ) else 0) +
    (if 30 = n then (140552804761600 : ℤ) else 0) +
    (if 28 = n then (-72155450572800 : ℤ) else 0) +
    (if 26 = n then (25426206392320 : ℤ) else 0) +
    (if 24 = n then (-5497558138880 : ℤ) else 0) +
    (if 22 = n then (549755813888 : ℤ) else 0)

theorem fixed_reversedT_typed_data_40 : reversedRow 63 fixedChebyshevTData_40 = fixedReversedTData_40 := by
  simp only [fixedChebyshevTData_40, fixedReversedTData_40, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-800 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (106400 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-5617920 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (156900480 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-2677768192 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (30429184000 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-243433472000 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (1424085811200 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-6254808268800 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (21002987765760 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-54553214976000 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (110292369408000 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-173752901959680 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (212364657950720 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (-199183403319296 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (140552804761600 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (-72155450572800 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (25426206392320 : ℤ) 36 (by decide),
    fixedTyped_reversedRow_monomial (-5497558138880 : ℤ) 38 (by decide),
    fixedTyped_reversedRow_monomial (549755813888 : ℤ) 40 (by decide)]

theorem fixed_reversedT_typed_coeff_40 (n : ℕ) :
    fixedReversedTData_40.coeff n = fixedReversedTCoeff_40 n := by
  simp only [fixedReversedTData_40, fixedReversedTCoeff_40, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_40 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_40 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_40, ite_eq_right, add_zero]

def fixedReversedTData_41 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (41 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-11480 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (959728 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-37840704 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (857722624 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-12475965440 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (124759654400 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-898269511680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (4808383856640 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-19570965872640 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (61508749885440 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-150732904857600 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (289407177326592 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-435347548798976 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (510407471005696 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-461013199618048 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (314327181557760 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-156371169312768 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (53532472377344 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-11269994184704 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (1099511627776 : ℤ)

def fixedReversedTCoeff_41 (n : ℕ) : ℤ :=
    (if 61 = n then (41 : ℤ) else 0) +
    (if 59 = n then (-11480 : ℤ) else 0) +
    (if 57 = n then (959728 : ℤ) else 0) +
    (if 55 = n then (-37840704 : ℤ) else 0) +
    (if 53 = n then (857722624 : ℤ) else 0) +
    (if 51 = n then (-12475965440 : ℤ) else 0) +
    (if 49 = n then (124759654400 : ℤ) else 0) +
    (if 47 = n then (-898269511680 : ℤ) else 0) +
    (if 45 = n then (4808383856640 : ℤ) else 0) +
    (if 43 = n then (-19570965872640 : ℤ) else 0) +
    (if 41 = n then (61508749885440 : ℤ) else 0) +
    (if 39 = n then (-150732904857600 : ℤ) else 0) +
    (if 37 = n then (289407177326592 : ℤ) else 0) +
    (if 35 = n then (-435347548798976 : ℤ) else 0) +
    (if 33 = n then (510407471005696 : ℤ) else 0) +
    (if 31 = n then (-461013199618048 : ℤ) else 0) +
    (if 29 = n then (314327181557760 : ℤ) else 0) +
    (if 27 = n then (-156371169312768 : ℤ) else 0) +
    (if 25 = n then (53532472377344 : ℤ) else 0) +
    (if 23 = n then (-11269994184704 : ℤ) else 0) +
    (if 21 = n then (1099511627776 : ℤ) else 0)

theorem fixed_reversedT_typed_data_41 : reversedRow 63 fixedChebyshevTData_41 = fixedReversedTData_41 := by
  simp only [fixedChebyshevTData_41, fixedReversedTData_41, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (41 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-11480 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (959728 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-37840704 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (857722624 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-12475965440 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (124759654400 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-898269511680 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (4808383856640 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-19570965872640 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (61508749885440 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-150732904857600 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (289407177326592 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (-435347548798976 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (510407471005696 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (-461013199618048 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (314327181557760 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (-156371169312768 : ℤ) 35 (by decide),
    fixedTyped_reversedRow_monomial (53532472377344 : ℤ) 37 (by decide),
    fixedTyped_reversedRow_monomial (-11269994184704 : ℤ) 39 (by decide),
    fixedTyped_reversedRow_monomial (1099511627776 : ℤ) 41 (by decide)]

theorem fixed_reversedT_typed_coeff_41 (n : ℕ) :
    fixedReversedTData_41.coeff n = fixedReversedTCoeff_41 n := by
  simp only [fixedReversedTData_41, fixedReversedTCoeff_41, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_41 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_41 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_41, ite_eq_right, add_zero]

def fixedReversedTData_42 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (882 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-129360 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (7537376 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-232581888 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (4393213440 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-55381114880 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (492952780800 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-3220624834560 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (15871575982080 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-60144919511040 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (177570714746880 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-411758179123200 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (752567256612864 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-1083059755548672 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (1219998345330688 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-1062579203997696 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (700809813688320 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-338168545017856 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (112562502893568 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-23089744183296 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (2199023255552 : ℤ)

def fixedReversedTCoeff_42 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (882 : ℤ) else 0) +
    (if 58 = n then (-129360 : ℤ) else 0) +
    (if 56 = n then (7537376 : ℤ) else 0) +
    (if 54 = n then (-232581888 : ℤ) else 0) +
    (if 52 = n then (4393213440 : ℤ) else 0) +
    (if 50 = n then (-55381114880 : ℤ) else 0) +
    (if 48 = n then (492952780800 : ℤ) else 0) +
    (if 46 = n then (-3220624834560 : ℤ) else 0) +
    (if 44 = n then (15871575982080 : ℤ) else 0) +
    (if 42 = n then (-60144919511040 : ℤ) else 0) +
    (if 40 = n then (177570714746880 : ℤ) else 0) +
    (if 38 = n then (-411758179123200 : ℤ) else 0) +
    (if 36 = n then (752567256612864 : ℤ) else 0) +
    (if 34 = n then (-1083059755548672 : ℤ) else 0) +
    (if 32 = n then (1219998345330688 : ℤ) else 0) +
    (if 30 = n then (-1062579203997696 : ℤ) else 0) +
    (if 28 = n then (700809813688320 : ℤ) else 0) +
    (if 26 = n then (-338168545017856 : ℤ) else 0) +
    (if 24 = n then (112562502893568 : ℤ) else 0) +
    (if 22 = n then (-23089744183296 : ℤ) else 0) +
    (if 20 = n then (2199023255552 : ℤ) else 0)

theorem fixed_reversedT_typed_data_42 : reversedRow 63 fixedChebyshevTData_42 = fixedReversedTData_42 := by
  simp only [fixedChebyshevTData_42, fixedReversedTData_42, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (882 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-129360 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (7537376 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-232581888 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (4393213440 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-55381114880 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (492952780800 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-3220624834560 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (15871575982080 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-60144919511040 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (177570714746880 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-411758179123200 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (752567256612864 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (-1083059755548672 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (1219998345330688 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (-1062579203997696 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (700809813688320 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (-338168545017856 : ℤ) 36 (by decide),
    fixedTyped_reversedRow_monomial (112562502893568 : ℤ) 38 (by decide),
    fixedTyped_reversedRow_monomial (-23089744183296 : ℤ) 40 (by decide),
    fixedTyped_reversedRow_monomial (2199023255552 : ℤ) 42 (by decide)]

theorem fixed_reversedT_typed_coeff_42 (n : ℕ) :
    fixedReversedTData_42.coeff n = fixedReversedTCoeff_42 n := by
  simp only [fixedReversedTData_42, fixedReversedTCoeff_42, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_42 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_42 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_42, ite_eq_right, add_zero]

def fixedReversedTData_43 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-43 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (13244 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-1218448 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (52915456 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1322886400 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (21262392320 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-235521884160 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (1884175073280 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-11249633525760 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (51314117836800 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-181798588907520 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (505874334351360 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-1112923535572992 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (1940482062024704 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-2676526982103040 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (2901009890279424 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-2439485589553152 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (1557990796689408 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-729869562413056 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (236394999971840 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-47278999994368 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (4398046511104 : ℤ)

def fixedReversedTCoeff_43 (n : ℕ) : ℤ :=
    (if 61 = n then (-43 : ℤ) else 0) +
    (if 59 = n then (13244 : ℤ) else 0) +
    (if 57 = n then (-1218448 : ℤ) else 0) +
    (if 55 = n then (52915456 : ℤ) else 0) +
    (if 53 = n then (-1322886400 : ℤ) else 0) +
    (if 51 = n then (21262392320 : ℤ) else 0) +
    (if 49 = n then (-235521884160 : ℤ) else 0) +
    (if 47 = n then (1884175073280 : ℤ) else 0) +
    (if 45 = n then (-11249633525760 : ℤ) else 0) +
    (if 43 = n then (51314117836800 : ℤ) else 0) +
    (if 41 = n then (-181798588907520 : ℤ) else 0) +
    (if 39 = n then (505874334351360 : ℤ) else 0) +
    (if 37 = n then (-1112923535572992 : ℤ) else 0) +
    (if 35 = n then (1940482062024704 : ℤ) else 0) +
    (if 33 = n then (-2676526982103040 : ℤ) else 0) +
    (if 31 = n then (2901009890279424 : ℤ) else 0) +
    (if 29 = n then (-2439485589553152 : ℤ) else 0) +
    (if 27 = n then (1557990796689408 : ℤ) else 0) +
    (if 25 = n then (-729869562413056 : ℤ) else 0) +
    (if 23 = n then (236394999971840 : ℤ) else 0) +
    (if 21 = n then (-47278999994368 : ℤ) else 0) +
    (if 19 = n then (4398046511104 : ℤ) else 0)

theorem fixed_reversedT_typed_data_43 : reversedRow 63 fixedChebyshevTData_43 = fixedReversedTData_43 := by
  simp only [fixedChebyshevTData_43, fixedReversedTData_43, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-43 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (13244 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-1218448 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (52915456 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-1322886400 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (21262392320 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-235521884160 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (1884175073280 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-11249633525760 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (51314117836800 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-181798588907520 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (505874334351360 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-1112923535572992 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (1940482062024704 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (-2676526982103040 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (2901009890279424 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (-2439485589553152 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (1557990796689408 : ℤ) 35 (by decide),
    fixedTyped_reversedRow_monomial (-729869562413056 : ℤ) 37 (by decide),
    fixedTyped_reversedRow_monomial (236394999971840 : ℤ) 39 (by decide),
    fixedTyped_reversedRow_monomial (-47278999994368 : ℤ) 41 (by decide),
    fixedTyped_reversedRow_monomial (4398046511104 : ℤ) 43 (by decide)]

theorem fixed_reversedT_typed_coeff_43 (n : ℕ) :
    fixedReversedTData_43.coeff n = fixedReversedTCoeff_43 n := by
  simp only [fixedReversedTData_43, fixedReversedTCoeff_43, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_43 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_43 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_43, ite_eq_right, add_zero]

def fixedReversedTData_44 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-968 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (155848 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-9974272 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (338412800 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-7038986240 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (97905899520 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-963996549120 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (6988974981120 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-38370843033600 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (162773155184640 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-541167892561920 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (1423506847825920 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-2978414327758848 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (4964023879598080 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-6573052309536768 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (6864598984556544 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-5579780992794624 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (3454150138396672 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-1572301627719680 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (495879744126976 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (-96757023244288 : ℤ) +
    Polynomial.monomial (R := ℤ) 18 (8796093022208 : ℤ)

def fixedReversedTCoeff_44 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-968 : ℤ) else 0) +
    (if 58 = n then (155848 : ℤ) else 0) +
    (if 56 = n then (-9974272 : ℤ) else 0) +
    (if 54 = n then (338412800 : ℤ) else 0) +
    (if 52 = n then (-7038986240 : ℤ) else 0) +
    (if 50 = n then (97905899520 : ℤ) else 0) +
    (if 48 = n then (-963996549120 : ℤ) else 0) +
    (if 46 = n then (6988974981120 : ℤ) else 0) +
    (if 44 = n then (-38370843033600 : ℤ) else 0) +
    (if 42 = n then (162773155184640 : ℤ) else 0) +
    (if 40 = n then (-541167892561920 : ℤ) else 0) +
    (if 38 = n then (1423506847825920 : ℤ) else 0) +
    (if 36 = n then (-2978414327758848 : ℤ) else 0) +
    (if 34 = n then (4964023879598080 : ℤ) else 0) +
    (if 32 = n then (-6573052309536768 : ℤ) else 0) +
    (if 30 = n then (6864598984556544 : ℤ) else 0) +
    (if 28 = n then (-5579780992794624 : ℤ) else 0) +
    (if 26 = n then (3454150138396672 : ℤ) else 0) +
    (if 24 = n then (-1572301627719680 : ℤ) else 0) +
    (if 22 = n then (495879744126976 : ℤ) else 0) +
    (if 20 = n then (-96757023244288 : ℤ) else 0) +
    (if 18 = n then (8796093022208 : ℤ) else 0)

theorem fixed_reversedT_typed_data_44 : reversedRow 63 fixedChebyshevTData_44 = fixedReversedTData_44 := by
  simp only [fixedChebyshevTData_44, fixedReversedTData_44, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-968 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (155848 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-9974272 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (338412800 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-7038986240 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (97905899520 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-963996549120 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (6988974981120 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-38370843033600 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (162773155184640 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-541167892561920 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (1423506847825920 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-2978414327758848 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (4964023879598080 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (-6573052309536768 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (6864598984556544 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (-5579780992794624 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (3454150138396672 : ℤ) 36 (by decide),
    fixedTyped_reversedRow_monomial (-1572301627719680 : ℤ) 38 (by decide),
    fixedTyped_reversedRow_monomial (495879744126976 : ℤ) 40 (by decide),
    fixedTyped_reversedRow_monomial (-96757023244288 : ℤ) 42 (by decide),
    fixedTyped_reversedRow_monomial (8796093022208 : ℤ) 44 (by decide)]

theorem fixed_reversedT_typed_coeff_44 (n : ℕ) :
    fixedReversedTData_44.coeff n = fixedReversedTCoeff_44 n := by
  simp only [fixedReversedTData_44, fixedReversedTCoeff_44, coeff_add, coeff_monomial]

theorem fixed_reversedT_typed_tail_44 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedTCoeff_44 n = 0 := by
  simp (disch := omega) only [fixedReversedTCoeff_44, ite_eq_right, add_zero]

end InternalCatalan

end

end OAI
