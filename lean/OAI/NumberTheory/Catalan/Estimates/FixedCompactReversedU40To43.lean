import OAI.NumberTheory.Catalan.Estimates.FixedCompactReversedT0To7

namespace OAI


noncomputable section
open Polynomial
namespace InternalCatalan

def fixedReversedUData_40 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (-840 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (117040 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (-6460608 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (188280576 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (-3347210240 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (39557939200 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (-328635187200 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (1993720135680 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (-9069471989760 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (31504481648640 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (-84557483212800 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (176467791052800 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (-286692288233472 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (361019918516224 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (-348570955808768 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (252995048570880 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (-133487583559680 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (48309792145408 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (-10720238370816 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (1099511627776 : ℤ)

def fixedReversedUCoeff_40 (n : ℕ) : ℤ :=
    (if 62 = n then (1 : ℤ) else 0) +
    (if 60 = n then (-840 : ℤ) else 0) +
    (if 58 = n then (117040 : ℤ) else 0) +
    (if 56 = n then (-6460608 : ℤ) else 0) +
    (if 54 = n then (188280576 : ℤ) else 0) +
    (if 52 = n then (-3347210240 : ℤ) else 0) +
    (if 50 = n then (39557939200 : ℤ) else 0) +
    (if 48 = n then (-328635187200 : ℤ) else 0) +
    (if 46 = n then (1993720135680 : ℤ) else 0) +
    (if 44 = n then (-9069471989760 : ℤ) else 0) +
    (if 42 = n then (31504481648640 : ℤ) else 0) +
    (if 40 = n then (-84557483212800 : ℤ) else 0) +
    (if 38 = n then (176467791052800 : ℤ) else 0) +
    (if 36 = n then (-286692288233472 : ℤ) else 0) +
    (if 34 = n then (361019918516224 : ℤ) else 0) +
    (if 32 = n then (-348570955808768 : ℤ) else 0) +
    (if 30 = n then (252995048570880 : ℤ) else 0) +
    (if 28 = n then (-133487583559680 : ℤ) else 0) +
    (if 26 = n then (48309792145408 : ℤ) else 0) +
    (if 24 = n then (-10720238370816 : ℤ) else 0) +
    (if 22 = n then (1099511627776 : ℤ) else 0)

theorem fixed_reversedU_typed_data_40 : reversedRow 63 fixedChebyshevUData_40 = fixedReversedUData_40 := by
  simp only [fixedChebyshevUData_40, fixedReversedUData_40, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (-840 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (117040 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (-6460608 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (188280576 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (-3347210240 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (39557939200 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (-328635187200 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (1993720135680 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (-9069471989760 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (31504481648640 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (-84557483212800 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (176467791052800 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (-286692288233472 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (361019918516224 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (-348570955808768 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (252995048570880 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (-133487583559680 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (48309792145408 : ℤ) 36 (by decide),
    fixedTyped_reversedRow_monomial (-10720238370816 : ℤ) 38 (by decide),
    fixedTyped_reversedRow_monomial (1099511627776 : ℤ) 40 (by decide)]

theorem fixed_reversedU_typed_coeff_40 (n : ℕ) :
    fixedReversedUData_40.coeff n = fixedReversedUCoeff_40 n := by
  simp only [fixedReversedUData_40, fixedReversedUCoeff_40, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_40 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_40 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_40, ite_eq_right, add_zero]

def fixedReversedUData_41 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (42 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (-12320 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (1076768 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (-44301312 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (1046003200 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (-15823175680 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (164317593600 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (-1226904698880 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (6802103992320 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (-28640437862400 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (93013231534080 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (-235290388070400 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (465874968379392 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (-722039837032448 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (871427389521920 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (-809584155426816 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (567322230128640 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (-289858752872448 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (101842264522752 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (-21990232555520 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (2199023255552 : ℤ)

def fixedReversedUCoeff_41 (n : ℕ) : ℤ :=
    (if 61 = n then (42 : ℤ) else 0) +
    (if 59 = n then (-12320 : ℤ) else 0) +
    (if 57 = n then (1076768 : ℤ) else 0) +
    (if 55 = n then (-44301312 : ℤ) else 0) +
    (if 53 = n then (1046003200 : ℤ) else 0) +
    (if 51 = n then (-15823175680 : ℤ) else 0) +
    (if 49 = n then (164317593600 : ℤ) else 0) +
    (if 47 = n then (-1226904698880 : ℤ) else 0) +
    (if 45 = n then (6802103992320 : ℤ) else 0) +
    (if 43 = n then (-28640437862400 : ℤ) else 0) +
    (if 41 = n then (93013231534080 : ℤ) else 0) +
    (if 39 = n then (-235290388070400 : ℤ) else 0) +
    (if 37 = n then (465874968379392 : ℤ) else 0) +
    (if 35 = n then (-722039837032448 : ℤ) else 0) +
    (if 33 = n then (871427389521920 : ℤ) else 0) +
    (if 31 = n then (-809584155426816 : ℤ) else 0) +
    (if 29 = n then (567322230128640 : ℤ) else 0) +
    (if 27 = n then (-289858752872448 : ℤ) else 0) +
    (if 25 = n then (101842264522752 : ℤ) else 0) +
    (if 23 = n then (-21990232555520 : ℤ) else 0) +
    (if 21 = n then (2199023255552 : ℤ) else 0)

theorem fixed_reversedU_typed_data_41 : reversedRow 63 fixedChebyshevUData_41 = fixedReversedUData_41 := by
  simp only [fixedChebyshevUData_41, fixedReversedUData_41, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (42 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (-12320 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (1076768 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (-44301312 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (1046003200 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (-15823175680 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (164317593600 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (-1226904698880 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (6802103992320 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (-28640437862400 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (93013231534080 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (-235290388070400 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (465874968379392 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (-722039837032448 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (871427389521920 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (-809584155426816 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (567322230128640 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (-289858752872448 : ℤ) 35 (by decide),
    fixedTyped_reversedRow_monomial (101842264522752 : ℤ) 37 (by decide),
    fixedTyped_reversedRow_monomial (-21990232555520 : ℤ) 39 (by decide),
    fixedTyped_reversedRow_monomial (2199023255552 : ℤ) 41 (by decide)]

theorem fixed_reversedU_typed_coeff_41 (n : ℕ) :
    fixedReversedUData_41.coeff n = fixedReversedUCoeff_41 n := by
  simp only [fixedReversedUData_41, fixedReversedUCoeff_41, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_41 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_41 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_41, ite_eq_right, add_zero]

def fixedReversedUData_42 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 62 (-1 : ℤ) +
    Polynomial.monomial (R := ℤ) 60 (924 : ℤ) +
    Polynomial.monomial (R := ℤ) 58 (-141680 : ℤ) +
    Polynomial.monomial (R := ℤ) 56 (8614144 : ℤ) +
    Polynomial.monomial (R := ℤ) 54 (-276883200 : ℤ) +
    Polynomial.monomial (R := ℤ) 52 (5439216640 : ℤ) +
    Polynomial.monomial (R := ℤ) 50 (-71204290560 : ℤ) +
    Polynomial.monomial (R := ℤ) 48 (657270374400 : ℤ) +
    Polynomial.monomial (R := ℤ) 46 (-4447529533440 : ℤ) +
    Polynomial.monomial (R := ℤ) 44 (22673679974400 : ℤ) +
    Polynomial.monomial (R := ℤ) 42 (-88785357373440 : ℤ) +
    Polynomial.monomial (R := ℤ) 40 (270583946280960 : ℤ) +
    Polynomial.monomial (R := ℤ) 38 (-647048567193600 : ℤ) +
    Polynomial.monomial (R := ℤ) 36 (1218442224992256 : ℤ) +
    Polynomial.monomial (R := ℤ) 34 (-1805099592581120 : ℤ) +
    Polynomial.monomial (R := ℤ) 32 (2091425734852608 : ℤ) +
    Polynomial.monomial (R := ℤ) 30 (-1872163359424512 : ℤ) +
    Polynomial.monomial (R := ℤ) 28 (1268132043816960 : ℤ) +
    Polynomial.monomial (R := ℤ) 26 (-628027297890304 : ℤ) +
    Polynomial.monomial (R := ℤ) 24 (214404767416320 : ℤ) +
    Polynomial.monomial (R := ℤ) 22 (-45079976738816 : ℤ) +
    Polynomial.monomial (R := ℤ) 20 (4398046511104 : ℤ)

def fixedReversedUCoeff_42 (n : ℕ) : ℤ :=
    (if 62 = n then (-1 : ℤ) else 0) +
    (if 60 = n then (924 : ℤ) else 0) +
    (if 58 = n then (-141680 : ℤ) else 0) +
    (if 56 = n then (8614144 : ℤ) else 0) +
    (if 54 = n then (-276883200 : ℤ) else 0) +
    (if 52 = n then (5439216640 : ℤ) else 0) +
    (if 50 = n then (-71204290560 : ℤ) else 0) +
    (if 48 = n then (657270374400 : ℤ) else 0) +
    (if 46 = n then (-4447529533440 : ℤ) else 0) +
    (if 44 = n then (22673679974400 : ℤ) else 0) +
    (if 42 = n then (-88785357373440 : ℤ) else 0) +
    (if 40 = n then (270583946280960 : ℤ) else 0) +
    (if 38 = n then (-647048567193600 : ℤ) else 0) +
    (if 36 = n then (1218442224992256 : ℤ) else 0) +
    (if 34 = n then (-1805099592581120 : ℤ) else 0) +
    (if 32 = n then (2091425734852608 : ℤ) else 0) +
    (if 30 = n then (-1872163359424512 : ℤ) else 0) +
    (if 28 = n then (1268132043816960 : ℤ) else 0) +
    (if 26 = n then (-628027297890304 : ℤ) else 0) +
    (if 24 = n then (214404767416320 : ℤ) else 0) +
    (if 22 = n then (-45079976738816 : ℤ) else 0) +
    (if 20 = n then (4398046511104 : ℤ) else 0)

theorem fixed_reversedU_typed_data_42 : reversedRow 63 fixedChebyshevUData_42 = fixedReversedUData_42 := by
  simp only [fixedChebyshevUData_42, fixedReversedUData_42, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-1 : ℤ) 0 (by decide),
    fixedTyped_reversedRow_monomial (924 : ℤ) 2 (by decide),
    fixedTyped_reversedRow_monomial (-141680 : ℤ) 4 (by decide),
    fixedTyped_reversedRow_monomial (8614144 : ℤ) 6 (by decide),
    fixedTyped_reversedRow_monomial (-276883200 : ℤ) 8 (by decide),
    fixedTyped_reversedRow_monomial (5439216640 : ℤ) 10 (by decide),
    fixedTyped_reversedRow_monomial (-71204290560 : ℤ) 12 (by decide),
    fixedTyped_reversedRow_monomial (657270374400 : ℤ) 14 (by decide),
    fixedTyped_reversedRow_monomial (-4447529533440 : ℤ) 16 (by decide),
    fixedTyped_reversedRow_monomial (22673679974400 : ℤ) 18 (by decide),
    fixedTyped_reversedRow_monomial (-88785357373440 : ℤ) 20 (by decide),
    fixedTyped_reversedRow_monomial (270583946280960 : ℤ) 22 (by decide),
    fixedTyped_reversedRow_monomial (-647048567193600 : ℤ) 24 (by decide),
    fixedTyped_reversedRow_monomial (1218442224992256 : ℤ) 26 (by decide),
    fixedTyped_reversedRow_monomial (-1805099592581120 : ℤ) 28 (by decide),
    fixedTyped_reversedRow_monomial (2091425734852608 : ℤ) 30 (by decide),
    fixedTyped_reversedRow_monomial (-1872163359424512 : ℤ) 32 (by decide),
    fixedTyped_reversedRow_monomial (1268132043816960 : ℤ) 34 (by decide),
    fixedTyped_reversedRow_monomial (-628027297890304 : ℤ) 36 (by decide),
    fixedTyped_reversedRow_monomial (214404767416320 : ℤ) 38 (by decide),
    fixedTyped_reversedRow_monomial (-45079976738816 : ℤ) 40 (by decide),
    fixedTyped_reversedRow_monomial (4398046511104 : ℤ) 42 (by decide)]

theorem fixed_reversedU_typed_coeff_42 (n : ℕ) :
    fixedReversedUData_42.coeff n = fixedReversedUCoeff_42 n := by
  simp only [fixedReversedUData_42, fixedReversedUCoeff_42, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_42 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_42 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_42, ite_eq_right, add_zero]

def fixedReversedUData_43 : ℤ[X] :=
    Polynomial.monomial (R := ℤ) 61 (-44 : ℤ) +
    Polynomial.monomial (R := ℤ) 59 (14168 : ℤ) +
    Polynomial.monomial (R := ℤ) 57 (-1360128 : ℤ) +
    Polynomial.monomial (R := ℤ) 55 (61529600 : ℤ) +
    Polynomial.monomial (R := ℤ) 53 (-1599769600 : ℤ) +
    Polynomial.monomial (R := ℤ) 51 (26701608960 : ℤ) +
    Polynomial.monomial (R := ℤ) 49 (-306726174720 : ℤ) +
    Polynomial.monomial (R := ℤ) 47 (2541445447680 : ℤ) +
    Polynomial.monomial (R := ℤ) 45 (-15697163059200 : ℤ) +
    Polynomial.monomial (R := ℤ) 43 (73987797811200 : ℤ) +
    Polynomial.monomial (R := ℤ) 41 (-270583946280960 : ℤ) +
    Polynomial.monomial (R := ℤ) 39 (776458280632320 : ℤ) +
    Polynomial.monomial (R := ℤ) 37 (-1759972102766592 : ℤ) +
    Polynomial.monomial (R := ℤ) 35 (3158924287016960 : ℤ) +
    Polynomial.monomial (R := ℤ) 33 (-4481626574684160 : ℤ) +
    Polynomial.monomial (R := ℤ) 31 (4992435625132032 : ℤ) +
    Polynomial.monomial (R := ℤ) 29 (-4311648948977664 : ℤ) +
    Polynomial.monomial (R := ℤ) 27 (2826122840506368 : ℤ) +
    Polynomial.monomial (R := ℤ) 25 (-1357896860303360 : ℤ) +
    Polynomial.monomial (R := ℤ) 23 (450799767388160 : ℤ) +
    Polynomial.monomial (R := ℤ) 21 (-92358976733184 : ℤ) +
    Polynomial.monomial (R := ℤ) 19 (8796093022208 : ℤ)

def fixedReversedUCoeff_43 (n : ℕ) : ℤ :=
    (if 61 = n then (-44 : ℤ) else 0) +
    (if 59 = n then (14168 : ℤ) else 0) +
    (if 57 = n then (-1360128 : ℤ) else 0) +
    (if 55 = n then (61529600 : ℤ) else 0) +
    (if 53 = n then (-1599769600 : ℤ) else 0) +
    (if 51 = n then (26701608960 : ℤ) else 0) +
    (if 49 = n then (-306726174720 : ℤ) else 0) +
    (if 47 = n then (2541445447680 : ℤ) else 0) +
    (if 45 = n then (-15697163059200 : ℤ) else 0) +
    (if 43 = n then (73987797811200 : ℤ) else 0) +
    (if 41 = n then (-270583946280960 : ℤ) else 0) +
    (if 39 = n then (776458280632320 : ℤ) else 0) +
    (if 37 = n then (-1759972102766592 : ℤ) else 0) +
    (if 35 = n then (3158924287016960 : ℤ) else 0) +
    (if 33 = n then (-4481626574684160 : ℤ) else 0) +
    (if 31 = n then (4992435625132032 : ℤ) else 0) +
    (if 29 = n then (-4311648948977664 : ℤ) else 0) +
    (if 27 = n then (2826122840506368 : ℤ) else 0) +
    (if 25 = n then (-1357896860303360 : ℤ) else 0) +
    (if 23 = n then (450799767388160 : ℤ) else 0) +
    (if 21 = n then (-92358976733184 : ℤ) else 0) +
    (if 19 = n then (8796093022208 : ℤ) else 0)

theorem fixed_reversedU_typed_data_43 : reversedRow 63 fixedChebyshevUData_43 = fixedReversedUData_43 := by
  simp only [fixedChebyshevUData_43, fixedReversedUData_43, fixedTyped_reversedRow_add]
  rw [fixedTyped_reversedRow_monomial (-44 : ℤ) 1 (by decide),
    fixedTyped_reversedRow_monomial (14168 : ℤ) 3 (by decide),
    fixedTyped_reversedRow_monomial (-1360128 : ℤ) 5 (by decide),
    fixedTyped_reversedRow_monomial (61529600 : ℤ) 7 (by decide),
    fixedTyped_reversedRow_monomial (-1599769600 : ℤ) 9 (by decide),
    fixedTyped_reversedRow_monomial (26701608960 : ℤ) 11 (by decide),
    fixedTyped_reversedRow_monomial (-306726174720 : ℤ) 13 (by decide),
    fixedTyped_reversedRow_monomial (2541445447680 : ℤ) 15 (by decide),
    fixedTyped_reversedRow_monomial (-15697163059200 : ℤ) 17 (by decide),
    fixedTyped_reversedRow_monomial (73987797811200 : ℤ) 19 (by decide),
    fixedTyped_reversedRow_monomial (-270583946280960 : ℤ) 21 (by decide),
    fixedTyped_reversedRow_monomial (776458280632320 : ℤ) 23 (by decide),
    fixedTyped_reversedRow_monomial (-1759972102766592 : ℤ) 25 (by decide),
    fixedTyped_reversedRow_monomial (3158924287016960 : ℤ) 27 (by decide),
    fixedTyped_reversedRow_monomial (-4481626574684160 : ℤ) 29 (by decide),
    fixedTyped_reversedRow_monomial (4992435625132032 : ℤ) 31 (by decide),
    fixedTyped_reversedRow_monomial (-4311648948977664 : ℤ) 33 (by decide),
    fixedTyped_reversedRow_monomial (2826122840506368 : ℤ) 35 (by decide),
    fixedTyped_reversedRow_monomial (-1357896860303360 : ℤ) 37 (by decide),
    fixedTyped_reversedRow_monomial (450799767388160 : ℤ) 39 (by decide),
    fixedTyped_reversedRow_monomial (-92358976733184 : ℤ) 41 (by decide),
    fixedTyped_reversedRow_monomial (8796093022208 : ℤ) 43 (by decide)]

theorem fixed_reversedU_typed_coeff_43 (n : ℕ) :
    fixedReversedUData_43.coeff n = fixedReversedUCoeff_43 n := by
  simp only [fixedReversedUData_43, fixedReversedUCoeff_43, coeff_add, coeff_monomial]

theorem fixed_reversedU_typed_tail_43 (n : ℕ) (hn : 63 ≤ n) :
    fixedReversedUCoeff_43 n = 0 := by
  simp (disch := omega) only [fixedReversedUCoeff_43, ite_eq_right, add_zero]

end InternalCatalan

end

end OAI
