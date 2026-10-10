import OAI.LinearAlgebra.MatrixMultiplication.Numerical.ComplexRationalLogCertificate

namespace OAI

/-! Fixed rational distributions and their entropy and capacity formulas. -/

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

abbrev Shape := Fin 3 → ℕ

def shape (a b c : ℕ) : Shape := ![a, b, c]

def shapes (n : ℕ) : List Shape :=
  (List.range (n + 1)).flatMap fun a =>
    (List.range (n + 1 - a)).map fun b => shape a b (n - a - b)

def positive (s : Shape) : Bool := s 0 > 0 && s 1 > 0 && s 2 > 0

def sorted (s : Shape) : Bool := s 0 ≤ s 1 && s 1 ≤ s 2

def sortedInitial : List Shape := (shapes 16).filter sorted

def positiveInitial : List Shape := sortedInitial.filter positive

def positiveSecond : List Shape := (shapes 8).filter positive

def zeroSecond : List Shape := (shapes 8).filter (fun s => !positive s)

def shapeMax (s : Shape) : ℕ := max (s 0) (max (s 1) (s 2))

def below (s : Shape) : List Shape :=
  (shapes ((s 0 + s 1 + s 2) / 2)).filter
    (fun u => u 0 ≤ s 0 && u 1 ≤ s 1 && u 2 ≤ s 2)

def complement (s u : Shape) : Shape := fun i => s i - u i

def tablea : List ℤ :=
  [-55839, -36137, -17449, -1780, 11561, 22640, 31188, 36731, 38593, 35898,
   29051, 18387, 3823, -14569, -39776, -38598, -23708]

def tableP : List ℤ :=
  [-3070, 295, -20546, -1514, -38211, -9654, -7530, -2765, -55230, -16412,
   -14246, -5912, -78106, -32809, -7009, -26324, -13519, -3592, -96458, -47439,
   -16217, -46871, -25058, -9643, -95643, -62269, -28725, -8576, -2535, -2550,
   -34711, -7207, -3270, -6376, -53221, -15352, -3477, -14828, -4187, -74924,
   -32439, -7231, -3578, -24599, -8700, -92989, -46655, -16926, -3517, -42976,
   -20283, -5132, -107049, -63201, -31013, -9730, -3705, -67421, -35684, -13735,
   -68829, -36752, -13993, -7658, -7586, -76746, -33496, -7329, -7447, -17336,
   -4721, -96770, -49297, -17874, -7143, -30044, -10107, -116558, -68325, -33467,
   -10424, -7476, -51341, -24711, -5530, -76548, -41988, -15608, -17266, -4357,
   -17106, -4343, -120770, -70820, -34294, -10580, -16819, -4315, -32943, -9992,
   -83616, -44202, -16154, -17098, -4371, -56609, -25990, -5564, -56356, -25900,
   -5561, -33052, -9918, -32951, -9906, -57255, -26128, -5560]

def tablep : List ℤ :=
  [-39594, -5561, -55254, -15178, -62331, -19672, -54917, -18539, -16455, -32184,
   -5716, -11688, -5527, -53009, -6669, -6669, -64938, -20286, -6616, -26336,
   -26429, -6696, -60888, -19760, -6690, -5724, -32216, -15829, -58477, -18987,
   -26339, -6619, -26393, -26340, -26359, -6620, -16239, -55176, -18587, -55107,
   -18571, -16272, -60868, -19755, -6696, -6692, -55133, -18580, -16247, -32128,
   -5727, -32138, -5725, -122]

def tabled : List ℤ :=
  [63, 97655, 0, 42132, 92966, 1204, 42148, 95604, 41743, 3057,
   109933, 42092, 3747, 41991, 1, 100622, 42166, 103562, 9039, 42157,
   103577, 42165, 63582, 110082, 4584, 42175, 104091, 38838, 102383, 104793,
   42126, 11814, 63338, 42165, 104864, 3587, 42166, 110086, 2207, 94768,
   42166, 104185, 4735, 38889, 110065, 42166, 102372, 104314, 38956, 4876,
   102395, 42166, 110068, 2953, 42166, 96000, 41863, 95723, 3031, 63321,
   42040, 42174, 104662, 11860, 104902, 42189, 2967, 96042, 42047, 109872,
   3986, 42200, 3834, 110106, 60257]

def tablez : List ℤ :=
  [-11037, -36170, -4779, 23107, -12831, 29263, 45052, 22289, -6216, 23895,
   -14326, -40670, -9623, -34674, -12708, -36610, -2174, 21564, -5587, 22521,
   -9766, 28961, 43809, 22299, -12216, 28778, 44147, 22176, -7811, 21870,
   -6053, 23786, -166, 94, -52, 17]

theorem table_lengths :
    [tablea.length, tableP.length, tablep.length, tabled.length, tablez.length] =
      [17, 118, 54, 75, 36] := by decide +kernel

theorem parent_counts :
    [sortedInitial.length, positiveInitial.length, positiveSecond.length,
      zeroSecond.length] = [30, 21, 21, 24] := by decide +kernel

def statisticWeight : Fin 6 → ℕ := ![0, 1, 2, 2, 3, 4]

def multiplicity : Fin 6 → ℕ := ![1, 10, 25, 2, 10, 1]

def kappa : Fin 6 → Fin 6 := ![5, 4, 2, 3, 1, 0]

theorem kappa_involution (i : Fin 6) : kappa (kappa i) = i := by
  revert i
  decide +kernel

theorem multiplicity_kappa (i : Fin 6) : multiplicity (kappa i) = multiplicity i := by
  revert i
  decide +kernel

theorem statisticWeight_kappa (i : Fin 6) :
    statisticWeight (kappa i) = 4 - statisticWeight i := by
  revert i
  decide +kernel

def weight (n : ℤ) : ℚ :=
  (∑ j ∈ Finset.range 17, ((n : ℚ) / 640000) ^ j / Nat.factorial j) ^ 64

theorem weight_nonnegative (n : ℤ) : 0 ≤ weight n := by
  unfold weight
  positivity

abbrev SplitKey := Shape × Fin 3 × ℕ

def splitKeys (parents : List Shape) : List SplitKey :=
  parents.flatMap fun s =>
    ([0, 1, 2] : List (Fin 3)).flatMap fun i =>
      (List.range (s i / 2)).filterMap fun j =>
        if s i - (s 0 + s 1 + s 2) / 2 ≤ j then some (s, i, j) else none

def assigned {α : Type} [BEq α] (keys : List α) (data : List ℤ) (key : α) : ℤ :=
  (((keys.zip data).find? (fun e => e.1 == key)).map Prod.snd).getD 0

def splitSignature (parents : List Shape) (data : List ℤ) (s u : Shape) : Fin 3 → ℤ :=
  fun i => assigned (splitKeys parents) data (s, i, min (u i) (s i - u i))

def stageASignature := splitSignature positiveInitial tableP

def stageBSignature := splitSignature positiveSecond tablep

def splitWeight (parents : List Shape) (data : List ℤ) (s u : Shape) : ℚ :=
  ∏ i : Fin 3, weight (splitSignature parents data s u i)

def splitLaw (parents : List Shape) (data : List ℤ) (s u : Shape) : ℚ :=
  if u ∈ below s then
    splitWeight parents data s u / ((below s).map (splitWeight parents data s)).sum
  else 0

def stageALaw := splitLaw positiveInitial tableP

def stageBLaw := splitLaw positiveSecond tablep

theorem split_consumption :
    [(splitKeys positiveInitial).length, (splitKeys positiveSecond).length] =
      [118, 54] := by decide +kernel

theorem splitSignature_complement (parents : List Shape) (data : List ℤ)
    (s u : Shape) (h : ∀ i, u i ≤ s i) :
    splitSignature parents data s (complement s u) = splitSignature parents data s u := by
  funext i
  simp only [splitSignature, complement, Nat.sub_sub_self (h i), min_comm]

theorem splitWeight_complement (parents : List Shape) (data : List ℤ)
    (s u : Shape) (h : ∀ i, u i ≤ s i) :
    splitWeight parents data s (complement s u) = splitWeight parents data s u := by
  simp only [splitWeight, splitSignature_complement parents data s u h]

theorem splitLaw_complement (parents : List Shape) (data : List ℤ)
    (s u : Shape) (h : ∀ i, u i ≤ s i)
    (hu : u ∈ below s) (hc : complement s u ∈ below s) :
    splitLaw parents data s (complement s u) = splitLaw parents data s u := by
  simp only [splitLaw, hu, hc, ite_true, splitWeight_complement parents data s u h]

theorem splitLaw_outside_support (parents : List Shape) (data : List ℤ)
    (s u : Shape) (hu : u ∉ below s) : splitLaw parents data s u = 0 := by
  simp only [splitLaw, hu, ite_false]

def binaryKeys : List (Shape × Shape) :=
  positiveSecond.flatMap fun t =>
    ((below t).filter (fun u => shapeMax u == 2)).map fun u => (t, u)

def binaryInteger (t u : Shape) : ℤ := assigned binaryKeys tabled (t, u)

def binaryParameter (t u : Shape) : ℚ := (binaryInteger t u : ℚ) / 1000000

theorem binary_consumption : binaryKeys.length = 75 := by decide +kernel

theorem binary_table_range : tabled.all (fun n => 0 ≤ n && n ≤ 110106) = true := by
  decide +kernel

theorem complementary_binary_parameters_are_distinct :
    binaryInteger (shape 1 3 4) (shape 0 2 2) = 92966 ∧
    binaryInteger (shape 1 3 4) (shape 1 1 2) = 1204 := by decide +kernel

theorem unreachable_parent_retained : shape 6 1 1 ∈ positiveSecond := by decide +kernel

abbrev PairSlot := Fin 6 × Fin 6

def unorderedPairs (t : Shape) : List PairSlot :=
  (List.finRange 6).flatMap fun i =>
    (List.finRange 6).filterMap fun j =>
      if i ≤ j ∧ statisticWeight i + statisticWeight j = shapeMax t
      then some (i, j) else none

def pairKeys : List (Shape × PairSlot) :=
  zeroSecond.flatMap fun t =>
    ((unorderedPairs t).dropLast).map fun ij => (t, ij)

def orderedPairInteger (t : Shape) (i j : Fin 6) : ℤ :=
  assigned pairKeys tablez (t, min i j, max i j)

def orderedPairs (t : Shape) : List PairSlot :=
  (List.finRange 6).flatMap fun i =>
    (List.finRange 6).filterMap fun j =>
      if statisticWeight i + statisticWeight j = shapeMax t then some (i, j) else none

def zeroPairLaw (t : Shape) (i j : Fin 6) : ℚ :=
  if statisticWeight i + statisticWeight j = shapeMax t then
    weight (orderedPairInteger t i j) /
      ((orderedPairs t).map (fun ij => weight (orderedPairInteger t ij.1 ij.2))).sum
  else 0

theorem pair_consumption : pairKeys.length = 36 := by decide +kernel

theorem orderedPairInteger_swap (t : Shape) (i j : Fin 6) :
    orderedPairInteger t i j = orderedPairInteger t j i := by
  simp only [orderedPairInteger, min_comm, max_comm]

theorem zeroPairLaw_swap (t : Shape) (i j : Fin 6) :
    zeroPairLaw t i j = zeroPairLaw t j i := by
  simp only [zeroPairLaw, orderedPairInteger_swap t i j, add_comm]

theorem zeroPairLaw_outside_support (t : Shape) (i j : Fin 6)
    (h : statisticWeight i + statisticWeight j ≠ shapeMax t) :
    zeroPairLaw t i j = 0 := by
  simp only [zeroPairLaw, h, ite_false]

end MatrixMultiplication.AllFieldParameters

end OAI
