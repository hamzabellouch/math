import OAI.Analysis.Quantum.PPTSquare.MatrixInverse

namespace OAI

noncomputable section
open scoped BigOperators
open Matrix
namespace PencilAlgebra
lemma N0_N1_row0 : ∀ j : Fin 20, (N0Num * N1Num) 0 j = (N1Num * N0Num) 0 j := by decide
lemma N0_N1_row1 : ∀ j : Fin 20, (N0Num * N1Num) 1 j = (N1Num * N0Num) 1 j := by decide
lemma N0_N1_row2 : ∀ j : Fin 20, (N0Num * N1Num) 2 j = (N1Num * N0Num) 2 j := by decide
lemma N0_N1_row3 : ∀ j : Fin 20, (N0Num * N1Num) 3 j = (N1Num * N0Num) 3 j := by decide
lemma N0_N1_row4 : ∀ j : Fin 20, (N0Num * N1Num) 4 j = (N1Num * N0Num) 4 j := by decide
lemma N0_N1_row5 : ∀ j : Fin 20, (N0Num * N1Num) 5 j = (N1Num * N0Num) 5 j := by decide
lemma N0_N1_row6 : ∀ j : Fin 20, (N0Num * N1Num) 6 j = (N1Num * N0Num) 6 j := by decide
lemma N0_N1_row7 : ∀ j : Fin 20, (N0Num * N1Num) 7 j = (N1Num * N0Num) 7 j := by decide
lemma N0_N1_row8 : ∀ j : Fin 20, (N0Num * N1Num) 8 j = (N1Num * N0Num) 8 j := by decide
lemma N0_N1_row9 : ∀ j : Fin 20, (N0Num * N1Num) 9 j = (N1Num * N0Num) 9 j := by decide
lemma N0_N1_row10 : ∀ j : Fin 20, (N0Num * N1Num) 10 j = (N1Num * N0Num) 10 j := by decide
lemma N0_N1_row11 : ∀ j : Fin 20, (N0Num * N1Num) 11 j = (N1Num * N0Num) 11 j := by decide
lemma N0_N1_row12 : ∀ j : Fin 20, (N0Num * N1Num) 12 j = (N1Num * N0Num) 12 j := by decide
lemma N0_N1_row13 : ∀ j : Fin 20, (N0Num * N1Num) 13 j = (N1Num * N0Num) 13 j := by decide
lemma N0_N1_row14 : ∀ j : Fin 20, (N0Num * N1Num) 14 j = (N1Num * N0Num) 14 j := by decide
lemma N0_N1_row15 : ∀ j : Fin 20, (N0Num * N1Num) 15 j = (N1Num * N0Num) 15 j := by decide
lemma N0_N1_row16 : ∀ j : Fin 20, (N0Num * N1Num) 16 j = (N1Num * N0Num) 16 j := by decide
lemma N0_N1_row17 : ∀ j : Fin 20, (N0Num * N1Num) 17 j = (N1Num * N0Num) 17 j := by decide
lemma N0_N1_row18 : ∀ j : Fin 20, (N0Num * N1Num) 18 j = (N1Num * N0Num) 18 j := by decide
lemma N0_N1_row19 : ∀ j : Fin 20, (N0Num * N1Num) 19 j = (N1Num * N0Num) 19 j := by decide
lemma N0_N1 : N0Num * N1Num = N1Num * N0Num := by
  ext i j
  fin_cases i
  · exact N0_N1_row0 j
  · exact N0_N1_row1 j
  · exact N0_N1_row2 j
  · exact N0_N1_row3 j
  · exact N0_N1_row4 j
  · exact N0_N1_row5 j
  · exact N0_N1_row6 j
  · exact N0_N1_row7 j
  · exact N0_N1_row8 j
  · exact N0_N1_row9 j
  · exact N0_N1_row10 j
  · exact N0_N1_row11 j
  · exact N0_N1_row12 j
  · exact N0_N1_row13 j
  · exact N0_N1_row14 j
  · exact N0_N1_row15 j
  · exact N0_N1_row16 j
  · exact N0_N1_row17 j
  · exact N0_N1_row18 j
  · exact N0_N1_row19 j
lemma N0_N2_row0 : ∀ j : Fin 20, (N0Num * N2Num) 0 j = (N2Num * N0Num) 0 j := by decide
lemma N0_N2_row1 : ∀ j : Fin 20, (N0Num * N2Num) 1 j = (N2Num * N0Num) 1 j := by decide
lemma N0_N2_row2 : ∀ j : Fin 20, (N0Num * N2Num) 2 j = (N2Num * N0Num) 2 j := by decide
lemma N0_N2_row3 : ∀ j : Fin 20, (N0Num * N2Num) 3 j = (N2Num * N0Num) 3 j := by decide
lemma N0_N2_row4 : ∀ j : Fin 20, (N0Num * N2Num) 4 j = (N2Num * N0Num) 4 j := by decide
lemma N0_N2_row5 : ∀ j : Fin 20, (N0Num * N2Num) 5 j = (N2Num * N0Num) 5 j := by decide
lemma N0_N2_row6 : ∀ j : Fin 20, (N0Num * N2Num) 6 j = (N2Num * N0Num) 6 j := by decide
lemma N0_N2_row7 : ∀ j : Fin 20, (N0Num * N2Num) 7 j = (N2Num * N0Num) 7 j := by decide
lemma N0_N2_row8 : ∀ j : Fin 20, (N0Num * N2Num) 8 j = (N2Num * N0Num) 8 j := by decide
lemma N0_N2_row9 : ∀ j : Fin 20, (N0Num * N2Num) 9 j = (N2Num * N0Num) 9 j := by decide
lemma N0_N2_row10 : ∀ j : Fin 20, (N0Num * N2Num) 10 j = (N2Num * N0Num) 10 j := by decide
lemma N0_N2_row11 : ∀ j : Fin 20, (N0Num * N2Num) 11 j = (N2Num * N0Num) 11 j := by decide
lemma N0_N2_row12 : ∀ j : Fin 20, (N0Num * N2Num) 12 j = (N2Num * N0Num) 12 j := by decide
lemma N0_N2_row13 : ∀ j : Fin 20, (N0Num * N2Num) 13 j = (N2Num * N0Num) 13 j := by decide
lemma N0_N2_row14 : ∀ j : Fin 20, (N0Num * N2Num) 14 j = (N2Num * N0Num) 14 j := by decide
lemma N0_N2_row15 : ∀ j : Fin 20, (N0Num * N2Num) 15 j = (N2Num * N0Num) 15 j := by decide
lemma N0_N2_row16 : ∀ j : Fin 20, (N0Num * N2Num) 16 j = (N2Num * N0Num) 16 j := by decide
lemma N0_N2_row17 : ∀ j : Fin 20, (N0Num * N2Num) 17 j = (N2Num * N0Num) 17 j := by decide
lemma N0_N2_row18 : ∀ j : Fin 20, (N0Num * N2Num) 18 j = (N2Num * N0Num) 18 j := by decide
lemma N0_N2_row19 : ∀ j : Fin 20, (N0Num * N2Num) 19 j = (N2Num * N0Num) 19 j := by decide
lemma N0_N2 : N0Num * N2Num = N2Num * N0Num := by
  ext i j
  fin_cases i
  · exact N0_N2_row0 j
  · exact N0_N2_row1 j
  · exact N0_N2_row2 j
  · exact N0_N2_row3 j
  · exact N0_N2_row4 j
  · exact N0_N2_row5 j
  · exact N0_N2_row6 j
  · exact N0_N2_row7 j
  · exact N0_N2_row8 j
  · exact N0_N2_row9 j
  · exact N0_N2_row10 j
  · exact N0_N2_row11 j
  · exact N0_N2_row12 j
  · exact N0_N2_row13 j
  · exact N0_N2_row14 j
  · exact N0_N2_row15 j
  · exact N0_N2_row16 j
  · exact N0_N2_row17 j
  · exact N0_N2_row18 j
  · exact N0_N2_row19 j
lemma N1_N2_row0 : ∀ j : Fin 20, (N1Num * N2Num) 0 j = (N2Num * N1Num) 0 j := by decide
lemma N1_N2_row1 : ∀ j : Fin 20, (N1Num * N2Num) 1 j = (N2Num * N1Num) 1 j := by decide
lemma N1_N2_row2 : ∀ j : Fin 20, (N1Num * N2Num) 2 j = (N2Num * N1Num) 2 j := by decide
lemma N1_N2_row3 : ∀ j : Fin 20, (N1Num * N2Num) 3 j = (N2Num * N1Num) 3 j := by decide
lemma N1_N2_row4 : ∀ j : Fin 20, (N1Num * N2Num) 4 j = (N2Num * N1Num) 4 j := by decide
lemma N1_N2_row5 : ∀ j : Fin 20, (N1Num * N2Num) 5 j = (N2Num * N1Num) 5 j := by decide
lemma N1_N2_row6 : ∀ j : Fin 20, (N1Num * N2Num) 6 j = (N2Num * N1Num) 6 j := by decide
lemma N1_N2_row7 : ∀ j : Fin 20, (N1Num * N2Num) 7 j = (N2Num * N1Num) 7 j := by decide
lemma N1_N2_row8 : ∀ j : Fin 20, (N1Num * N2Num) 8 j = (N2Num * N1Num) 8 j := by decide
lemma N1_N2_row9 : ∀ j : Fin 20, (N1Num * N2Num) 9 j = (N2Num * N1Num) 9 j := by decide
lemma N1_N2_row10 : ∀ j : Fin 20, (N1Num * N2Num) 10 j = (N2Num * N1Num) 10 j := by decide
lemma N1_N2_row11 : ∀ j : Fin 20, (N1Num * N2Num) 11 j = (N2Num * N1Num) 11 j := by decide
lemma N1_N2_row12 : ∀ j : Fin 20, (N1Num * N2Num) 12 j = (N2Num * N1Num) 12 j := by decide
lemma N1_N2_row13 : ∀ j : Fin 20, (N1Num * N2Num) 13 j = (N2Num * N1Num) 13 j := by decide
lemma N1_N2_row14 : ∀ j : Fin 20, (N1Num * N2Num) 14 j = (N2Num * N1Num) 14 j := by decide
lemma N1_N2_row15 : ∀ j : Fin 20, (N1Num * N2Num) 15 j = (N2Num * N1Num) 15 j := by decide
lemma N1_N2_row16 : ∀ j : Fin 20, (N1Num * N2Num) 16 j = (N2Num * N1Num) 16 j := by decide
lemma N1_N2_row17 : ∀ j : Fin 20, (N1Num * N2Num) 17 j = (N2Num * N1Num) 17 j := by decide
lemma N1_N2_row18 : ∀ j : Fin 20, (N1Num * N2Num) 18 j = (N2Num * N1Num) 18 j := by decide
lemma N1_N2_row19 : ∀ j : Fin 20, (N1Num * N2Num) 19 j = (N2Num * N1Num) 19 j := by decide
lemma N1_N2 : N1Num * N2Num = N2Num * N1Num := by
  ext i j
  fin_cases i
  · exact N1_N2_row0 j
  · exact N1_N2_row1 j
  · exact N1_N2_row2 j
  · exact N1_N2_row3 j
  · exact N1_N2_row4 j
  · exact N1_N2_row5 j
  · exact N1_N2_row6 j
  · exact N1_N2_row7 j
  · exact N1_N2_row8 j
  · exact N1_N2_row9 j
  · exact N1_N2_row10 j
  · exact N1_N2_row11 j
  · exact N1_N2_row12 j
  · exact N1_N2_row13 j
  · exact N1_N2_row14 j
  · exact N1_N2_row15 j
  · exact N1_N2_row16 j
  · exact N1_N2_row17 j
  · exact N1_N2_row18 j
  · exact N1_N2_row19 j

end PencilAlgebra

end

end OAI
