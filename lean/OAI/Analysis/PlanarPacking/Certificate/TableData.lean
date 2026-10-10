import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

open scoped BigOperators
namespace SharpPlanar


noncomputable def tableRaw : ℕ → ℤ × ℤ × ℤ × ℤ
  | 1 => (-670689128, -6398628799, -250018302, 4107732082)
  | 3 => (93524468, 564897270, -186215974, -65204793)
  | 4 => (-64146977, 121133118, 82882809, -327822296)
  | 7 => (-1358193, -16329465, 1979670, 21637038)
  | 9 => (-2932910, -940875, 3636920, 2145806)
  | 12 => (3646952, -34846939, -6005382, 34369042)
  | 13 => (3183411, 63030995, -574123, -75237042)
  | 15 => (11390977, 27049982, -11312377, -34985096)
  | 16 => (-5593246, 13405071, 5915710, -10980954)
  | 19 => (54905, -1515007, -120136, 1498351)
  | 21 => (-210208, -634307, 177992, 747946)
  | 24 => (976077, -804949, -1037705, 105643)
  | 25 => (-824472, 7003719, 1011732, -6510015)
  | 27 => (611891, 4536095, -428528, -4440927)
  | 28 => (-472882, -107613, 399655, 403751)
  | 31 => (30744, -112653, -31773, 90515)
  | 33 => (-4974, -105568, 1240, 99081)
  | 36 => (128313, 246018, -114876, -267388)
  | 37 => (-176685, 505187, 166591, -396209)
  | 39 => (-21638, 472037, 32128, -402283)
  | 40 => (-18461, -165597, 10836, 164974)
  | 43 => (4565, -2296, -4050, 547)
  | 45 => (1477, -10734, -1524, 8978)
  | 48 => (10748, 50050, -8611, -45048)
  | 49 => (-20506, 7495, 17354, -266)
  | 51 => (-10361, 29035, 9641, -21534)
  | 52 => (2121, -26523, -2269, 23159)
  | 55 => (425, 858, -344, -839)
  | 57 => (302, -632, -266, 463)
  | 60 => (382, 5658, -231, -4688)
  | 61 => (-1481, -4320, 1140, 4098)
  | 63 => (-1494, -352, 1265, 647)
  | 64 => (558, -2609, -491, 2114)
  | 67 => (21, 169, -14, -145)
  | 69 => (34, 13, -28, -18)
  | 72 => (-55, 394, 53, -301)
  | 73 => (-21, -805, 5, 685)
  | 75 => (-136, -379, 108, 338)
  | 76 => (70, -144, -58, 104)
  | 79 => (-1, 19, 1, -15)
  | 81 => (2, 9, -2, -8)
  | 84 => (-13, 3, 11, 0)
  | 85 => (13, -87, -11, 70)
  | 87 => (-6, -60, 4, 49)
  | 88 => (6, 5, -4, -5)
  | 91 => (0, 1, 0, -1)
  | 93 => (0, 1, 0, -1)
  | 96 => (-2, -4, 1, 3)
  | 97 => (2, -6, -2, 4)
  | 99 => (0, -6, 0, 5)
  | 100 => (0, 2, 0, -2)
  | _ => (0,0,0,0)

noncomputable def tableC (i : Bool) (n : ℕ) : ℚ :=
  if n = 0 then (if i then 0 else 1)
  else (if i then (tableRaw n).2.2.1 else (tableRaw n).1)/10000000000

noncomputable def tableD (i : Bool) (n : ℕ) : ℚ :=
  if n = 0 then (if i then -46/125 else 11/25)
  else (if i then (tableRaw n).2.2.2 else (tableRaw n).2.1)/10000000000

noncomputable def tableConstant (i : Bool) : ℚ := if i then 17/1000 else -13/1000

noncomputable def tableNodes : Finset ℕ := {1, 3, 4, 7, 9, 12, 13, 15, 16, 19, 21, 24, 25, 27, 28, 31, 33, 36, 37, 39, 40, 43, 45, 48, 49, 51, 52, 55, 57, 60, 61, 63, 64, 67, 69, 72, 73, 75, 76, 79, 81, 84, 85, 87, 88, 91, 93, 96, 97, 99, 100}

noncomputable def tableAllNodes : Finset ℕ := insert 0 tableNodes

noncomputable def tableNorm (i : Bool) : ℚ :=
  ∑ n ∈ tableAllNodes, (|tableC i n| + |tableD i n|)

noncomputable def tableTailNorm (i : Bool) : ℚ :=
  ∑ n ∈ tableAllNodes.filter (40 < ·), (|tableC i n| + |tableD i n|)

lemma tableNorm_false : tableNorm false = 22516666247/10000000000 := by
  decide +kernel

lemma tableNorm_true : tableNorm true = 8927477314/10000000000 := by
  decide +kernel

lemma tableTailNorm_false : tableTailNorm false = 197471/10000000000 := by
  decide +kernel

lemma tableTailNorm_true : tableTailNorm true = 161623/10000000000 := by
  decide +kernel

lemma tableNorm_lt (i : Bool) : tableNorm i < 229/100 := by
  cases i
  · rw [tableNorm_false]; norm_num
  · rw [tableNorm_true]; norm_num

lemma tableTailNorm_lt (i : Bool) : tableTailNorm i < 1/50000 := by
  cases i
  · rw [tableTailNorm_false]; norm_num
  · rw [tableTailNorm_true]; norm_num


noncomputable def rationalTailLower (i : Bool) : ℚ :=
  let σ : ℚ := if i then 1 else -1
  let ns := tableAllNodes.filter (· ≤ 40)
  σ * tableConstant i +
    min (∑ n ∈ ns, σ*tableD i n) 0 / (83/2) +
    ∑ n ∈ ns, (min (σ*tableC i n) 0 / (83/2-n)^2 +
      min (σ*tableD i n) 0 * n / ((83/2)*(83/2-n)))

lemma rationalTailLower_false : 12/1000 < rationalTailLower false := by
  decide +kernel

lemma rationalTailLower_true : 16/1000 < rationalTailLower true := by
  decide +kernel

end SharpPlanar

end OAI
