import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWWordDimensions
import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.Contractions

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

namespace MatrixMultiplication.CWWordDimensionParameters

open CWWordDimensions AllFieldParameters.Contractions

theorem table_eq_recursive : ∀ j : Fin 17,
    (coefficients[j.val]?.getD 0) = recursiveCoeff 8 j.val := by
  decide +kernel

theorem table_eq_polynomial (j : Fin 17) :
    (coefficients[j.val]?.getD 0) = (sitePolynomial ^ 8).coeff j.val := by
  rw [coeff_eq_recursive, table_eq_recursive]

theorem table_eq_card (j : Fin 17) :
    (coefficients[j.val]?.getD 0) =
      Fintype.card (WeightWords (Fin 8) j.val) := by
  have h := card_weightWords_fin 8 j.val
  rw [Fintype.card_eq_nat_card] at h ⊢
  exact (table_eq_recursive j).trans h.symm

theorem table_positive : ∀ j : Fin 17, 0 < (coefficients[j.val]?.getD 0) := by
  decide +kernel

theorem word_card_positive (j : Fin 17) :
    0 < Fintype.card (WeightWords (Fin 8) j.val) := by
  have h := table_eq_card j
  rw [Fintype.card_eq_nat_card] at h ⊢
  rw [← h]
  exact table_positive j

end MatrixMultiplication.CWWordDimensionParameters

end OAI
