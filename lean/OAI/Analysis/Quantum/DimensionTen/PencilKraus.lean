import OAI.Analysis.Quantum.DimensionTen.Kraus

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def pencilKraus (r : Fin 6) : Mat 4 := fun i j => blocks j r i

lemma pencilKraus_real (r : Fin 6) (i j : Fin 4) : star (pencilKraus r i j) = pencilKraus r i j := by
  simp [pencilKraus, blocks]

lemma pencilMap_kraus : pencilMap = krausMap pencilKraus := by
  funext A
  ext u v
  simp only [pencilMap, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, krausMap_entry,
    pencilKraus_real]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [pencilKraus]
  ring

lemma pencilMap_input_transpose (A : Mat 4) : pencilMap Aᵀ = pencilMap A := by
  simp only [pencilMap, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [blocks_transpose_mul_comm j i]

lemma pencilMap_output_transpose (A : Mat 4) : (pencilMap A)ᵀ = pencilMap A := by
  simp only [pencilMap, Matrix.transpose_sum, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [blocks_transpose_mul_comm j i]

lemma pencilMap_linear : IsComplexLinear pencilMap := by
  rw [pencilMap_kraus]
  exact krausMap_linear _

lemma pencilMap_cp : CompletelyPositive pencilMap := by
  rw [pencilMap_kraus]
  exact krausMap_cp _

end DimensionTen

end
end

end OAI
