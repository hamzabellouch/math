import OAI.Analysis.Quantum.PPTSquare.Commutators

namespace OAI

noncomputable section
open scoped BigOperators
open Matrix
namespace PencilAlgebra
def NNum : Fin 3 → Matrix (Fin 20) (Fin 20) ℤ := ![N0Num,N1Num,N2Num]
def lowNext : Fin 3 → Fin 10 → Fin 20 := ![![3,7,8,9,14,15,16,17,18,19],![2,5,6,8,11,12,13,15,16,18],![1,4,5,7,10,11,12,14,15,17]]
def highNext : Fin 3 → Fin 10 → Fin 15 := ![![5,6,7,8,9,10,11,12,13,14],![1,2,3,4,6,7,8,10,11,13],![0,1,2,3,5,6,7,9,10,12]]
lemma low_col_0_0 : ∀ i : Fin 20, NNum 0 i 0 = denominator * (Pi.single (lowNext 0 0) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_0_1 : ∀ i : Fin 20, NNum 0 i 1 = denominator * (Pi.single (lowNext 0 1) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_0_2 : ∀ i : Fin 20, NNum 0 i 2 = denominator * (Pi.single (lowNext 0 2) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_0_3 : ∀ i : Fin 20, NNum 0 i 3 = denominator * (Pi.single (lowNext 0 3) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_0_4 : ∀ i : Fin 20, NNum 0 i 4 = denominator * (Pi.single (lowNext 0 4) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_0_5 : ∀ i : Fin 20, NNum 0 i 5 = denominator * (Pi.single (lowNext 0 5) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_0_6 : ∀ i : Fin 20, NNum 0 i 6 = denominator * (Pi.single (lowNext 0 6) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_0_7 : ∀ i : Fin 20, NNum 0 i 7 = denominator * (Pi.single (lowNext 0 7) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_0_8 : ∀ i : Fin 20, NNum 0 i 8 = denominator * (Pi.single (lowNext 0 8) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_0_9 : ∀ i : Fin 20, NNum 0 i 9 = denominator * (Pi.single (lowNext 0 9) 1 : Fin 20 → ℤ) i := by decide
lemma high_col_0_0 : ∀ i : Fin 20, NNum 0 i 10 = CNum (highNext 0 0) i := by decide
lemma high_col_0_1 : ∀ i : Fin 20, NNum 0 i 11 = CNum (highNext 0 1) i := by decide
lemma high_col_0_2 : ∀ i : Fin 20, NNum 0 i 12 = CNum (highNext 0 2) i := by decide
lemma high_col_0_3 : ∀ i : Fin 20, NNum 0 i 13 = CNum (highNext 0 3) i := by decide
lemma high_col_0_4 : ∀ i : Fin 20, NNum 0 i 14 = CNum (highNext 0 4) i := by decide
lemma high_col_0_5 : ∀ i : Fin 20, NNum 0 i 15 = CNum (highNext 0 5) i := by decide
lemma high_col_0_6 : ∀ i : Fin 20, NNum 0 i 16 = CNum (highNext 0 6) i := by decide
lemma high_col_0_7 : ∀ i : Fin 20, NNum 0 i 17 = CNum (highNext 0 7) i := by decide
lemma high_col_0_8 : ∀ i : Fin 20, NNum 0 i 18 = CNum (highNext 0 8) i := by decide
lemma high_col_0_9 : ∀ i : Fin 20, NNum 0 i 19 = CNum (highNext 0 9) i := by decide
lemma low_col_1_0 : ∀ i : Fin 20, NNum 1 i 0 = denominator * (Pi.single (lowNext 1 0) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_1_1 : ∀ i : Fin 20, NNum 1 i 1 = denominator * (Pi.single (lowNext 1 1) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_1_2 : ∀ i : Fin 20, NNum 1 i 2 = denominator * (Pi.single (lowNext 1 2) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_1_3 : ∀ i : Fin 20, NNum 1 i 3 = denominator * (Pi.single (lowNext 1 3) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_1_4 : ∀ i : Fin 20, NNum 1 i 4 = denominator * (Pi.single (lowNext 1 4) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_1_5 : ∀ i : Fin 20, NNum 1 i 5 = denominator * (Pi.single (lowNext 1 5) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_1_6 : ∀ i : Fin 20, NNum 1 i 6 = denominator * (Pi.single (lowNext 1 6) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_1_7 : ∀ i : Fin 20, NNum 1 i 7 = denominator * (Pi.single (lowNext 1 7) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_1_8 : ∀ i : Fin 20, NNum 1 i 8 = denominator * (Pi.single (lowNext 1 8) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_1_9 : ∀ i : Fin 20, NNum 1 i 9 = denominator * (Pi.single (lowNext 1 9) 1 : Fin 20 → ℤ) i := by decide
lemma high_col_1_0 : ∀ i : Fin 20, NNum 1 i 10 = CNum (highNext 1 0) i := by decide
lemma high_col_1_1 : ∀ i : Fin 20, NNum 1 i 11 = CNum (highNext 1 1) i := by decide
lemma high_col_1_2 : ∀ i : Fin 20, NNum 1 i 12 = CNum (highNext 1 2) i := by decide
lemma high_col_1_3 : ∀ i : Fin 20, NNum 1 i 13 = CNum (highNext 1 3) i := by decide
lemma high_col_1_4 : ∀ i : Fin 20, NNum 1 i 14 = CNum (highNext 1 4) i := by decide
lemma high_col_1_5 : ∀ i : Fin 20, NNum 1 i 15 = CNum (highNext 1 5) i := by decide
lemma high_col_1_6 : ∀ i : Fin 20, NNum 1 i 16 = CNum (highNext 1 6) i := by decide
lemma high_col_1_7 : ∀ i : Fin 20, NNum 1 i 17 = CNum (highNext 1 7) i := by decide
lemma high_col_1_8 : ∀ i : Fin 20, NNum 1 i 18 = CNum (highNext 1 8) i := by decide
lemma high_col_1_9 : ∀ i : Fin 20, NNum 1 i 19 = CNum (highNext 1 9) i := by decide
lemma low_col_2_0 : ∀ i : Fin 20, NNum 2 i 0 = denominator * (Pi.single (lowNext 2 0) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_2_1 : ∀ i : Fin 20, NNum 2 i 1 = denominator * (Pi.single (lowNext 2 1) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_2_2 : ∀ i : Fin 20, NNum 2 i 2 = denominator * (Pi.single (lowNext 2 2) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_2_3 : ∀ i : Fin 20, NNum 2 i 3 = denominator * (Pi.single (lowNext 2 3) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_2_4 : ∀ i : Fin 20, NNum 2 i 4 = denominator * (Pi.single (lowNext 2 4) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_2_5 : ∀ i : Fin 20, NNum 2 i 5 = denominator * (Pi.single (lowNext 2 5) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_2_6 : ∀ i : Fin 20, NNum 2 i 6 = denominator * (Pi.single (lowNext 2 6) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_2_7 : ∀ i : Fin 20, NNum 2 i 7 = denominator * (Pi.single (lowNext 2 7) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_2_8 : ∀ i : Fin 20, NNum 2 i 8 = denominator * (Pi.single (lowNext 2 8) 1 : Fin 20 → ℤ) i := by decide
lemma low_col_2_9 : ∀ i : Fin 20, NNum 2 i 9 = denominator * (Pi.single (lowNext 2 9) 1 : Fin 20 → ℤ) i := by decide
lemma high_col_2_0 : ∀ i : Fin 20, NNum 2 i 10 = CNum (highNext 2 0) i := by decide
lemma high_col_2_1 : ∀ i : Fin 20, NNum 2 i 11 = CNum (highNext 2 1) i := by decide
lemma high_col_2_2 : ∀ i : Fin 20, NNum 2 i 12 = CNum (highNext 2 2) i := by decide
lemma high_col_2_3 : ∀ i : Fin 20, NNum 2 i 13 = CNum (highNext 2 3) i := by decide
lemma high_col_2_4 : ∀ i : Fin 20, NNum 2 i 14 = CNum (highNext 2 4) i := by decide
lemma high_col_2_5 : ∀ i : Fin 20, NNum 2 i 15 = CNum (highNext 2 5) i := by decide
lemma high_col_2_6 : ∀ i : Fin 20, NNum 2 i 16 = CNum (highNext 2 6) i := by decide
lemma high_col_2_7 : ∀ i : Fin 20, NNum 2 i 17 = CNum (highNext 2 7) i := by decide
lemma high_col_2_8 : ∀ i : Fin 20, NNum 2 i 18 = CNum (highNext 2 8) i := by decide
lemma high_col_2_9 : ∀ i : Fin 20, NNum 2 i 19 = CNum (highNext 2 9) i := by decide
lemma low_col (a : Fin 3) (j : Fin 10) (i : Fin 20) : NNum a i (j.castLE (by decide)) = denominator * (Pi.single (lowNext a j) 1 : Fin 20 → ℤ) i := by
  fin_cases a <;> fin_cases j
  · exact low_col_0_0 i
  · exact low_col_0_1 i
  · exact low_col_0_2 i
  · exact low_col_0_3 i
  · exact low_col_0_4 i
  · exact low_col_0_5 i
  · exact low_col_0_6 i
  · exact low_col_0_7 i
  · exact low_col_0_8 i
  · exact low_col_0_9 i
  · exact low_col_1_0 i
  · exact low_col_1_1 i
  · exact low_col_1_2 i
  · exact low_col_1_3 i
  · exact low_col_1_4 i
  · exact low_col_1_5 i
  · exact low_col_1_6 i
  · exact low_col_1_7 i
  · exact low_col_1_8 i
  · exact low_col_1_9 i
  · exact low_col_2_0 i
  · exact low_col_2_1 i
  · exact low_col_2_2 i
  · exact low_col_2_3 i
  · exact low_col_2_4 i
  · exact low_col_2_5 i
  · exact low_col_2_6 i
  · exact low_col_2_7 i
  · exact low_col_2_8 i
  · exact low_col_2_9 i
lemma high_col (a : Fin 3) (j : Fin 10) (i : Fin 20) : NNum a i (j.natAdd 10) = CNum (highNext a j) i := by
  fin_cases a <;> fin_cases j
  · exact high_col_0_0 i
  · exact high_col_0_1 i
  · exact high_col_0_2 i
  · exact high_col_0_3 i
  · exact high_col_0_4 i
  · exact high_col_0_5 i
  · exact high_col_0_6 i
  · exact high_col_0_7 i
  · exact high_col_0_8 i
  · exact high_col_0_9 i
  · exact high_col_1_0 i
  · exact high_col_1_1 i
  · exact high_col_1_2 i
  · exact high_col_1_3 i
  · exact high_col_1_4 i
  · exact high_col_1_5 i
  · exact high_col_1_6 i
  · exact high_col_1_7 i
  · exact high_col_1_8 i
  · exact high_col_1_9 i
  · exact high_col_2_0 i
  · exact high_col_2_1 i
  · exact high_col_2_2 i
  · exact high_col_2_3 i
  · exact high_col_2_4 i
  · exact high_col_2_5 i
  · exact high_col_2_6 i
  · exact high_col_2_7 i
  · exact high_col_2_8 i
  · exact high_col_2_9 i
end PencilAlgebra

end

end OAI
