import OAI.Analysis.Quantum.PPTSquare.AlgebraData

namespace OAI

section
noncomputable section
open Matrix
namespace DimensionTen.Border
def H : Matrix (Fin 15) (Fin 15) ℤ := PencilAlgebra.H

def D : Matrix (Fin 15) (Fin 20) ℤ := PencilAlgebra.D

def adjH : Matrix (Fin 15) (Fin 15) ℤ := PencilAlgebra.HinvNum

def Cnum : Matrix (Fin 15) (Fin 20) ℤ :=
  fun i j => PencilAlgebra.CNum i j / 56594923448507739622342656

def d : ℤ := PencilAlgebra.denominator / 56594923448507739622342656
def detH : ℤ := PencilAlgebra.denominator

def B0 : Matrix (Fin 20) (Fin 20) ℤ :=
  fun i j => PencilAlgebra.N0Num i j / 56594923448507739622342656

def B1 : Matrix (Fin 20) (Fin 20) ℤ :=
  fun i j => PencilAlgebra.N1Num i j / 56594923448507739622342656

def B2 : Matrix (Fin 20) (Fin 20) ℤ :=
  fun i j => PencilAlgebra.N2Num i j / 56594923448507739622342656

def B : Fin 3 → Matrix (Fin 20) (Fin 20) ℤ := ![B0, B1, B2]

def monExps : Fin 35 → Fin 3 → ℕ :=
  ![![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![1, 0, 0], ![0, 0, 2], ![0, 1, 1], ![0, 2, 0], ![1, 0, 1], ![1, 1, 0], ![2, 0, 0], ![0, 0, 3], ![0, 1, 2], ![0, 2, 1], ![0, 3, 0], ![1, 0, 2], ![1, 1, 1], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0], ![3, 0, 0], ![0, 0, 4], ![0, 1, 3], ![0, 2, 2], ![0, 3, 1], ![0, 4, 0], ![1, 0, 3], ![1, 1, 2], ![1, 2, 1], ![1, 3, 0], ![2, 0, 2], ![2, 1, 1], ![2, 2, 0], ![3, 0, 1], ![3, 1, 0], ![4, 0, 0]]

def mon {R : Type*} [CommRing R] (t : Fin 3 → R) (i : Fin 35) : R :=
  ∏ j : Fin 3, t j ^ monExps i j

def low {R : Type*} [CommRing R] (t : Fin 3 → R) : Fin 20 → R :=
  fun i => mon t (Fin.castLE (by decide) i)

def high {R : Type*} [CommRing R] (t : Fin 3 → R) : Fin 15 → R :=
  fun i => mon t (i.natAdd 20)

lemma commute_01_row0 : ∀ k : Fin 20, (B0 * B1) 0 k = (B1 * B0) 0 k := by decide +kernel
lemma commute_01_row1 : ∀ k : Fin 20, (B0 * B1) 1 k = (B1 * B0) 1 k := by decide +kernel
lemma commute_01_row2 : ∀ k : Fin 20, (B0 * B1) 2 k = (B1 * B0) 2 k := by decide +kernel
lemma commute_01_row3 : ∀ k : Fin 20, (B0 * B1) 3 k = (B1 * B0) 3 k := by decide +kernel
lemma commute_01_row4 : ∀ k : Fin 20, (B0 * B1) 4 k = (B1 * B0) 4 k := by decide +kernel
lemma commute_01_row5 : ∀ k : Fin 20, (B0 * B1) 5 k = (B1 * B0) 5 k := by decide +kernel
lemma commute_01_row6 : ∀ k : Fin 20, (B0 * B1) 6 k = (B1 * B0) 6 k := by decide +kernel
lemma commute_01_row7 : ∀ k : Fin 20, (B0 * B1) 7 k = (B1 * B0) 7 k := by decide +kernel
lemma commute_01_row8 : ∀ k : Fin 20, (B0 * B1) 8 k = (B1 * B0) 8 k := by decide +kernel
lemma commute_01_row9 : ∀ k : Fin 20, (B0 * B1) 9 k = (B1 * B0) 9 k := by decide +kernel
lemma commute_01_row10 : ∀ k : Fin 20, (B0 * B1) 10 k = (B1 * B0) 10 k := by decide +kernel
lemma commute_01_row11 : ∀ k : Fin 20, (B0 * B1) 11 k = (B1 * B0) 11 k := by decide +kernel
lemma commute_01_row12 : ∀ k : Fin 20, (B0 * B1) 12 k = (B1 * B0) 12 k := by decide +kernel
lemma commute_01_row13 : ∀ k : Fin 20, (B0 * B1) 13 k = (B1 * B0) 13 k := by decide +kernel
lemma commute_01_row14 : ∀ k : Fin 20, (B0 * B1) 14 k = (B1 * B0) 14 k := by decide +kernel
lemma commute_01_row15 : ∀ k : Fin 20, (B0 * B1) 15 k = (B1 * B0) 15 k := by decide +kernel
lemma commute_01_row16 : ∀ k : Fin 20, (B0 * B1) 16 k = (B1 * B0) 16 k := by decide +kernel
lemma commute_01_row17 : ∀ k : Fin 20, (B0 * B1) 17 k = (B1 * B0) 17 k := by decide +kernel
lemma commute_01_row18 : ∀ k : Fin 20, (B0 * B1) 18 k = (B1 * B0) 18 k := by decide +kernel
lemma commute_01_row19 : ∀ k : Fin 20, (B0 * B1) 19 k = (B1 * B0) 19 k := by decide +kernel
lemma commute_01 : B0 * B1 = B1 * B0 := by
  ext i j
  fin_cases i
  · exact commute_01_row0 j
  · exact commute_01_row1 j
  · exact commute_01_row2 j
  · exact commute_01_row3 j
  · exact commute_01_row4 j
  · exact commute_01_row5 j
  · exact commute_01_row6 j
  · exact commute_01_row7 j
  · exact commute_01_row8 j
  · exact commute_01_row9 j
  · exact commute_01_row10 j
  · exact commute_01_row11 j
  · exact commute_01_row12 j
  · exact commute_01_row13 j
  · exact commute_01_row14 j
  · exact commute_01_row15 j
  · exact commute_01_row16 j
  · exact commute_01_row17 j
  · exact commute_01_row18 j
  · exact commute_01_row19 j

lemma commute_02_row0 : ∀ k : Fin 20, (B0 * B2) 0 k = (B2 * B0) 0 k := by decide +kernel
lemma commute_02_row1 : ∀ k : Fin 20, (B0 * B2) 1 k = (B2 * B0) 1 k := by decide +kernel
lemma commute_02_row2 : ∀ k : Fin 20, (B0 * B2) 2 k = (B2 * B0) 2 k := by decide +kernel
lemma commute_02_row3 : ∀ k : Fin 20, (B0 * B2) 3 k = (B2 * B0) 3 k := by decide +kernel
lemma commute_02_row4 : ∀ k : Fin 20, (B0 * B2) 4 k = (B2 * B0) 4 k := by decide +kernel
lemma commute_02_row5 : ∀ k : Fin 20, (B0 * B2) 5 k = (B2 * B0) 5 k := by decide +kernel
lemma commute_02_row6 : ∀ k : Fin 20, (B0 * B2) 6 k = (B2 * B0) 6 k := by decide +kernel
lemma commute_02_row7 : ∀ k : Fin 20, (B0 * B2) 7 k = (B2 * B0) 7 k := by decide +kernel
lemma commute_02_row8 : ∀ k : Fin 20, (B0 * B2) 8 k = (B2 * B0) 8 k := by decide +kernel
lemma commute_02_row9 : ∀ k : Fin 20, (B0 * B2) 9 k = (B2 * B0) 9 k := by decide +kernel
lemma commute_02_row10 : ∀ k : Fin 20, (B0 * B2) 10 k = (B2 * B0) 10 k := by decide +kernel
lemma commute_02_row11 : ∀ k : Fin 20, (B0 * B2) 11 k = (B2 * B0) 11 k := by decide +kernel
lemma commute_02_row12 : ∀ k : Fin 20, (B0 * B2) 12 k = (B2 * B0) 12 k := by decide +kernel
lemma commute_02_row13 : ∀ k : Fin 20, (B0 * B2) 13 k = (B2 * B0) 13 k := by decide +kernel
lemma commute_02_row14 : ∀ k : Fin 20, (B0 * B2) 14 k = (B2 * B0) 14 k := by decide +kernel
lemma commute_02_row15 : ∀ k : Fin 20, (B0 * B2) 15 k = (B2 * B0) 15 k := by decide +kernel
lemma commute_02_row16 : ∀ k : Fin 20, (B0 * B2) 16 k = (B2 * B0) 16 k := by decide +kernel
lemma commute_02_row17 : ∀ k : Fin 20, (B0 * B2) 17 k = (B2 * B0) 17 k := by decide +kernel
lemma commute_02_row18 : ∀ k : Fin 20, (B0 * B2) 18 k = (B2 * B0) 18 k := by decide +kernel
lemma commute_02_row19 : ∀ k : Fin 20, (B0 * B2) 19 k = (B2 * B0) 19 k := by decide +kernel
lemma commute_02 : B0 * B2 = B2 * B0 := by
  ext i j
  fin_cases i
  · exact commute_02_row0 j
  · exact commute_02_row1 j
  · exact commute_02_row2 j
  · exact commute_02_row3 j
  · exact commute_02_row4 j
  · exact commute_02_row5 j
  · exact commute_02_row6 j
  · exact commute_02_row7 j
  · exact commute_02_row8 j
  · exact commute_02_row9 j
  · exact commute_02_row10 j
  · exact commute_02_row11 j
  · exact commute_02_row12 j
  · exact commute_02_row13 j
  · exact commute_02_row14 j
  · exact commute_02_row15 j
  · exact commute_02_row16 j
  · exact commute_02_row17 j
  · exact commute_02_row18 j
  · exact commute_02_row19 j

lemma commute_12_row0 : ∀ k : Fin 20, (B1 * B2) 0 k = (B2 * B1) 0 k := by decide +kernel
lemma commute_12_row1 : ∀ k : Fin 20, (B1 * B2) 1 k = (B2 * B1) 1 k := by decide +kernel
lemma commute_12_row2 : ∀ k : Fin 20, (B1 * B2) 2 k = (B2 * B1) 2 k := by decide +kernel
lemma commute_12_row3 : ∀ k : Fin 20, (B1 * B2) 3 k = (B2 * B1) 3 k := by decide +kernel
lemma commute_12_row4 : ∀ k : Fin 20, (B1 * B2) 4 k = (B2 * B1) 4 k := by decide +kernel
lemma commute_12_row5 : ∀ k : Fin 20, (B1 * B2) 5 k = (B2 * B1) 5 k := by decide +kernel
lemma commute_12_row6 : ∀ k : Fin 20, (B1 * B2) 6 k = (B2 * B1) 6 k := by decide +kernel
lemma commute_12_row7 : ∀ k : Fin 20, (B1 * B2) 7 k = (B2 * B1) 7 k := by decide +kernel
lemma commute_12_row8 : ∀ k : Fin 20, (B1 * B2) 8 k = (B2 * B1) 8 k := by decide +kernel
lemma commute_12_row9 : ∀ k : Fin 20, (B1 * B2) 9 k = (B2 * B1) 9 k := by decide +kernel
lemma commute_12_row10 : ∀ k : Fin 20, (B1 * B2) 10 k = (B2 * B1) 10 k := by decide +kernel
lemma commute_12_row11 : ∀ k : Fin 20, (B1 * B2) 11 k = (B2 * B1) 11 k := by decide +kernel
lemma commute_12_row12 : ∀ k : Fin 20, (B1 * B2) 12 k = (B2 * B1) 12 k := by decide +kernel
lemma commute_12_row13 : ∀ k : Fin 20, (B1 * B2) 13 k = (B2 * B1) 13 k := by decide +kernel
lemma commute_12_row14 : ∀ k : Fin 20, (B1 * B2) 14 k = (B2 * B1) 14 k := by decide +kernel
lemma commute_12_row15 : ∀ k : Fin 20, (B1 * B2) 15 k = (B2 * B1) 15 k := by decide +kernel
lemma commute_12_row16 : ∀ k : Fin 20, (B1 * B2) 16 k = (B2 * B1) 16 k := by decide +kernel
lemma commute_12_row17 : ∀ k : Fin 20, (B1 * B2) 17 k = (B2 * B1) 17 k := by decide +kernel
lemma commute_12_row18 : ∀ k : Fin 20, (B1 * B2) 18 k = (B2 * B1) 18 k := by decide +kernel
lemma commute_12_row19 : ∀ k : Fin 20, (B1 * B2) 19 k = (B2 * B1) 19 k := by decide +kernel
lemma commute_12 : B1 * B2 = B2 * B1 := by
  ext i j
  fin_cases i
  · exact commute_12_row0 j
  · exact commute_12_row1 j
  · exact commute_12_row2 j
  · exact commute_12_row3 j
  · exact commute_12_row4 j
  · exact commute_12_row5 j
  · exact commute_12_row6 j
  · exact commute_12_row7 j
  · exact commute_12_row8 j
  · exact commute_12_row9 j
  · exact commute_12_row10 j
  · exact commute_12_row11 j
  · exact commute_12_row12 j
  · exact commute_12_row13 j
  · exact commute_12_row14 j
  · exact commute_12_row15 j
  · exact commute_12_row16 j
  · exact commute_12_row17 j
  · exact commute_12_row18 j
  · exact commute_12_row19 j

lemma inverse_row0 : ∀ k : Fin 15, (adjH * H) 0 k = (detH • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 0 k := by decide +kernel
lemma inverse_row1 : ∀ k : Fin 15, (adjH * H) 1 k = (detH • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 1 k := by decide +kernel
lemma inverse_row2 : ∀ k : Fin 15, (adjH * H) 2 k = (detH • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 2 k := by decide +kernel
lemma inverse_row3 : ∀ k : Fin 15, (adjH * H) 3 k = (detH • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 3 k := by decide +kernel
lemma inverse_row4 : ∀ k : Fin 15, (adjH * H) 4 k = (detH • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 4 k := by decide +kernel
lemma inverse_row5 : ∀ k : Fin 15, (adjH * H) 5 k = (detH • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 5 k := by decide +kernel
lemma inverse_row6 : ∀ k : Fin 15, (adjH * H) 6 k = (detH • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 6 k := by decide +kernel
lemma inverse_row7 : ∀ k : Fin 15, (adjH * H) 7 k = (detH • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 7 k := by decide +kernel
lemma inverse_row8 : ∀ k : Fin 15, (adjH * H) 8 k = (detH • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 8 k := by decide +kernel
lemma inverse_row9 : ∀ k : Fin 15, (adjH * H) 9 k = (detH • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 9 k := by decide +kernel
lemma inverse_row10 : ∀ k : Fin 15, (adjH * H) 10 k = (detH • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 10 k := by decide +kernel
lemma inverse_row11 : ∀ k : Fin 15, (adjH * H) 11 k = (detH • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 11 k := by decide +kernel
lemma inverse_row12 : ∀ k : Fin 15, (adjH * H) 12 k = (detH • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 12 k := by decide +kernel
lemma inverse_row13 : ∀ k : Fin 15, (adjH * H) 13 k = (detH • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 13 k := by decide +kernel
lemma inverse_row14 : ∀ k : Fin 15, (adjH * H) 14 k = (detH • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 14 k := by decide +kernel
lemma inverse : adjH * H = detH • (1 : Matrix (Fin 15) (Fin 15) ℤ) := by
  ext i j
  fin_cases i
  · exact inverse_row0 j
  · exact inverse_row1 j
  · exact inverse_row2 j
  · exact inverse_row3 j
  · exact inverse_row4 j
  · exact inverse_row5 j
  · exact inverse_row6 j
  · exact inverse_row7 j
  · exact inverse_row8 j
  · exact inverse_row9 j
  · exact inverse_row10 j
  · exact inverse_row11 j
  · exact inverse_row12 j
  · exact inverse_row13 j
  · exact inverse_row14 j
lemma relation_row0 : ∀ k : Fin 20, (H * Cnum) 0 k = (-(d • D)) 0 k := by decide +kernel
lemma relation_row1 : ∀ k : Fin 20, (H * Cnum) 1 k = (-(d • D)) 1 k := by decide +kernel
lemma relation_row2 : ∀ k : Fin 20, (H * Cnum) 2 k = (-(d • D)) 2 k := by decide +kernel
lemma relation_row3 : ∀ k : Fin 20, (H * Cnum) 3 k = (-(d • D)) 3 k := by decide +kernel
lemma relation_row4 : ∀ k : Fin 20, (H * Cnum) 4 k = (-(d • D)) 4 k := by decide +kernel
lemma relation_row5 : ∀ k : Fin 20, (H * Cnum) 5 k = (-(d • D)) 5 k := by decide +kernel
lemma relation_row6 : ∀ k : Fin 20, (H * Cnum) 6 k = (-(d • D)) 6 k := by decide +kernel
lemma relation_row7 : ∀ k : Fin 20, (H * Cnum) 7 k = (-(d • D)) 7 k := by decide +kernel
lemma relation_row8 : ∀ k : Fin 20, (H * Cnum) 8 k = (-(d • D)) 8 k := by decide +kernel
lemma relation_row9 : ∀ k : Fin 20, (H * Cnum) 9 k = (-(d • D)) 9 k := by decide +kernel
lemma relation_row10 : ∀ k : Fin 20, (H * Cnum) 10 k = (-(d • D)) 10 k := by decide +kernel
lemma relation_row11 : ∀ k : Fin 20, (H * Cnum) 11 k = (-(d • D)) 11 k := by decide +kernel
lemma relation_row12 : ∀ k : Fin 20, (H * Cnum) 12 k = (-(d • D)) 12 k := by decide +kernel
lemma relation_row13 : ∀ k : Fin 20, (H * Cnum) 13 k = (-(d • D)) 13 k := by decide +kernel
lemma relation_row14 : ∀ k : Fin 20, (H * Cnum) 14 k = (-(d • D)) 14 k := by decide +kernel
lemma relation : H * Cnum = -(d • D) := by
  ext i j
  fin_cases i
  · exact relation_row0 j
  · exact relation_row1 j
  · exact relation_row2 j
  · exact relation_row3 j
  · exact relation_row4 j
  · exact relation_row5 j
  · exact relation_row6 j
  · exact relation_row7 j
  · exact relation_row8 j
  · exact relation_row9 j
  · exact relation_row10 j
  · exact relation_row11 j
  · exact relation_row12 j
  · exact relation_row13 j
  · exact relation_row14 j

end DimensionTen.Border

end
end

end OAI
