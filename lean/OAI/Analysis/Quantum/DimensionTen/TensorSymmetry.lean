import OAI.Analysis.Quantum.DimensionTen.PencilModel

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma kronecker_transpose {a b c d : Type*} (A : Matrix a b ℂ) (B : Matrix c d ℂ) :
    (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ := rfl

lemma tensorMap_output_transpose {a b c d : ℕ} (F : Mat a → Mat b) (G : Mat c → Mat d)
    (hF : ∀ A, (F A)ᵀ = F A) (hG : ∀ A, (G A)ᵀ = G A)
    (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    (tensorMap F G X)ᵀ = tensorMap F G X := by
  simp only [tensorMap, Matrix.kronecker, Matrix.transpose_sum, kronecker_transpose, hG]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  erw [hF]

lemma tensorMap_input_transpose {a b c d : ℕ} (F : Mat a → Mat b) (G : Mat c → Mat d)
    (hF : ∀ A, F Aᵀ = F A) (hG : ∀ A, G Aᵀ = G A)
    (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    tensorMap F G Xᵀ = tensorMap F G X := by
  unfold tensorMap
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hb : (fun a b => Xᵀ (a, j) (b, i)) =
      (Matrix.of (fun a b => X (a, i) (b, j)))ᵀ := rfl
  rw [hb, hF]
  have hg : G (Matrix.single j i 1) = G (Matrix.single i j 1) := by
    have ht : (Matrix.single i j (1 : ℂ))ᵀ = Matrix.single j i 1 := by
      simp only [Matrix.transpose_single]
    rw [← ht, hG]
  rw [hg]
  rfl

lemma hsAdjoint_output_transpose {a b : ℕ} (F : Mat a → Mat b)
    (h : ∀ A, F Aᵀ = F A) (Y : Mat b) :
    (hsAdjoint F Y)ᵀ = hsAdjoint F Y := by
  ext i j
  change (∑ u, ∑ v, star (F (Matrix.single j i 1) u v) * Y u v) = _
  have he : F (Matrix.single j i 1) = F (Matrix.single i j 1) := by
    rw [← Matrix.transpose_single, h]
  rw [he]
  rfl

lemma symmetricIsometry_real : symmetricIsometryᴴ = symmetricIsometryᵀ := by
  ext i j
  simp [symmetricIsometry, Matrix.conjTranspose_apply, apply_ite star]

lemma exteriorIsometry_real : exteriorIsometryᴴ = exteriorIsometryᵀ := by
  ext i j
  simp [exteriorIsometry, Matrix.conjTranspose_apply]

lemma hodgeComplement_real : hodgeComplementᴴ = hodgeComplementᵀ := by
  ext i j
  change star (hodgeComplement j i) = hodgeComplement j i
  fin_cases i <;> fin_cases j <;> norm_num [hodgeComplement]

lemma hodgeComplement_symmetric : hodgeComplementᵀ = hodgeComplement := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma firstSix_real : firstSixᴴ = firstSixᵀ := by
  ext i j
  simp [firstSix, Matrix.conjTranspose_apply, apply_ite star]

lemma real_compression_transpose {a b : Type*} [Fintype a]
    (V : Matrix a b ℂ) (hV : Vᴴ = Vᵀ) (A : Matrix a a ℂ) :
    (Vᴴ * A * V)ᵀ = Vᴴ * Aᵀ * V := by
  simp only [Matrix.transpose_mul, hV, Matrix.transpose_transpose, Matrix.mul_assoc]

lemma real_embedding_transpose {a b : Type*} [Fintype a]
    (V : Matrix b a ℂ) (hV : Vᴴ = Vᵀ) (A : Matrix a a ℂ) :
    (V * A * Vᴴ)ᵀ = V * Aᵀ * Vᴴ := by
  simp only [Matrix.transpose_mul, hV, Matrix.transpose_transpose, Matrix.mul_assoc]

end DimensionTen

end
end

end OAI
