import OAI.Analysis.Quantum.PPTSquare.AlgebraData

namespace OAI

noncomputable section
open scoped BigOperators
open Matrix
namespace PencilAlgebra
lemma H_Hinv_row0 : ∀ j : Fin 15, (H * HinvNum) 0 j = (denominator • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 0 j := by decide
lemma H_C_row0 : ∀ j : Fin 20, (H * CNum) 0 j = - denominator * D 0 j := by decide
lemma H_Hinv_row1 : ∀ j : Fin 15, (H * HinvNum) 1 j = (denominator • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 1 j := by decide
lemma H_C_row1 : ∀ j : Fin 20, (H * CNum) 1 j = - denominator * D 1 j := by decide
lemma H_Hinv_row2 : ∀ j : Fin 15, (H * HinvNum) 2 j = (denominator • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 2 j := by decide
lemma H_C_row2 : ∀ j : Fin 20, (H * CNum) 2 j = - denominator * D 2 j := by decide
lemma H_Hinv_row3 : ∀ j : Fin 15, (H * HinvNum) 3 j = (denominator • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 3 j := by decide
lemma H_C_row3 : ∀ j : Fin 20, (H * CNum) 3 j = - denominator * D 3 j := by decide
lemma H_Hinv_row4 : ∀ j : Fin 15, (H * HinvNum) 4 j = (denominator • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 4 j := by decide
lemma H_C_row4 : ∀ j : Fin 20, (H * CNum) 4 j = - denominator * D 4 j := by decide
lemma H_Hinv_row5 : ∀ j : Fin 15, (H * HinvNum) 5 j = (denominator • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 5 j := by decide
lemma H_C_row5 : ∀ j : Fin 20, (H * CNum) 5 j = - denominator * D 5 j := by decide
lemma H_Hinv_row6 : ∀ j : Fin 15, (H * HinvNum) 6 j = (denominator • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 6 j := by decide
lemma H_C_row6 : ∀ j : Fin 20, (H * CNum) 6 j = - denominator * D 6 j := by decide
lemma H_Hinv_row7 : ∀ j : Fin 15, (H * HinvNum) 7 j = (denominator • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 7 j := by decide
lemma H_C_row7 : ∀ j : Fin 20, (H * CNum) 7 j = - denominator * D 7 j := by decide
lemma H_Hinv_row8 : ∀ j : Fin 15, (H * HinvNum) 8 j = (denominator • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 8 j := by decide
lemma H_C_row8 : ∀ j : Fin 20, (H * CNum) 8 j = - denominator * D 8 j := by decide
lemma H_Hinv_row9 : ∀ j : Fin 15, (H * HinvNum) 9 j = (denominator • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 9 j := by decide
lemma H_C_row9 : ∀ j : Fin 20, (H * CNum) 9 j = - denominator * D 9 j := by decide
lemma H_Hinv_row10 : ∀ j : Fin 15, (H * HinvNum) 10 j = (denominator • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 10 j := by decide
lemma H_C_row10 : ∀ j : Fin 20, (H * CNum) 10 j = - denominator * D 10 j := by decide
lemma H_Hinv_row11 : ∀ j : Fin 15, (H * HinvNum) 11 j = (denominator • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 11 j := by decide
lemma H_C_row11 : ∀ j : Fin 20, (H * CNum) 11 j = - denominator * D 11 j := by decide
lemma H_Hinv_row12 : ∀ j : Fin 15, (H * HinvNum) 12 j = (denominator • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 12 j := by decide
lemma H_C_row12 : ∀ j : Fin 20, (H * CNum) 12 j = - denominator * D 12 j := by decide
lemma H_Hinv_row13 : ∀ j : Fin 15, (H * HinvNum) 13 j = (denominator • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 13 j := by decide
lemma H_C_row13 : ∀ j : Fin 20, (H * CNum) 13 j = - denominator * D 13 j := by decide
lemma H_Hinv_row14 : ∀ j : Fin 15, (H * HinvNum) 14 j = (denominator • (1 : Matrix (Fin 15) (Fin 15) ℤ)) 14 j := by decide
lemma H_C_row14 : ∀ j : Fin 20, (H * CNum) 14 j = - denominator * D 14 j := by decide
lemma H_Hinv : H * HinvNum = denominator • 1 := by
  ext i j
  fin_cases i
  · exact H_Hinv_row0 j
  · exact H_Hinv_row1 j
  · exact H_Hinv_row2 j
  · exact H_Hinv_row3 j
  · exact H_Hinv_row4 j
  · exact H_Hinv_row5 j
  · exact H_Hinv_row6 j
  · exact H_Hinv_row7 j
  · exact H_Hinv_row8 j
  · exact H_Hinv_row9 j
  · exact H_Hinv_row10 j
  · exact H_Hinv_row11 j
  · exact H_Hinv_row12 j
  · exact H_Hinv_row13 j
  · exact H_Hinv_row14 j
lemma H_C : H * CNum = (-denominator) • D := by
  ext i j
  fin_cases i
  · exact H_C_row0 j
  · exact H_C_row1 j
  · exact H_C_row2 j
  · exact H_C_row3 j
  · exact H_C_row4 j
  · exact H_C_row5 j
  · exact H_C_row6 j
  · exact H_C_row7 j
  · exact H_C_row8 j
  · exact H_C_row9 j
  · exact H_C_row10 j
  · exact H_C_row11 j
  · exact H_C_row12 j
  · exact H_C_row13 j
  · exact H_C_row14 j
end PencilAlgebra

end

end OAI
