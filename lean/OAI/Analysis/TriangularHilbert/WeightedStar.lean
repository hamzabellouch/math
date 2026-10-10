import OAI.Analysis.TriangularHilbert.GaussianGram

namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def vertexRoot (g : Three → ι → ℝ) : Matrix (BlockSpace ι) (BlockSpace ι) ℂ :=
  Matrix.diagonal (fun a => (Real.sqrt (g a.1 a.2) : ℂ))

def weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) : Three → Matrix ι ι ℂ :=
  fun v i j => (Real.sqrt (g v i) : ℂ) * A v i j * (Real.sqrt (g (v+1) j) : ℂ)

omit [Fintype ι] in
lemma vertexRoot_star (g : Three → ι → ℝ) : (vertexRoot g)ᴴ = vertexRoot g := by
  unfold vertexRoot
  rw [Matrix.diagonal_conjTranspose]
  simp

lemma vertexRoot_sq (g : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    vertexRoot g * vertexRoot g = Matrix.diagonal (fun a => (g a.1 a.2 : ℂ)) := by
  rw [vertexRoot, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hg a.1 a.2)]

lemma vertexRoot_commute_vertexProj (g : Three → ι → ℝ) (v : Three) :
    vertexRoot g * vertexProj v = vertexProj v * vertexRoot g := by
  dsimp only [vertexRoot, vertexProj]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact mul_comm _ _

lemma triangle_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) :
    triangle (weightedArray A g) = vertexRoot g * triangle A * vertexRoot g := by
  ext ⟨v,i⟩ ⟨w,j⟩
  fin_cases v <;> fin_cases w <;>
    simp [triangle, triangleBlocks, blocks, weightedArray, vertexRoot,
      Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
      mul_comm, mul_left_comm, mul_assoc] <;> first | exact Or.inl (mul_comm _ _) | ring

lemma rowStar_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v : Three) :
    rowStar (weightedArray A g) v = vertexRoot g * rowStar A v * vertexRoot g := by
  unfold rowStar
  rw [triangle_weightedArray]
  simp only [← Matrix.mul_assoc]
  rw [← vertexRoot_commute_vertexProj]

lemma rowStar_apply (A : Three → Matrix ι ι ℂ) (v : Three) (a b : BlockSpace ι) :
    rowStar A v a b = if a.1 = v then triangleBlocks A a.1 b.1 a.2 b.2 else 0 := by
  simp [rowStar, vertexProj, triangle, blocks, Matrix.diagonal_mul, ite_mul]

lemma rowStar_eq_blocks (A : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar A v = blocks (fun a b => if a = v then triangleBlocks A a b else 0) := by
  exact rowStar_blocks A v

def rowBare (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v : Three) :=
  rowStar A v * vertexRoot g

def colBare (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v : Three) :=
  (rowStar A v)ᴴ * vertexRoot g

lemma starGram_weightedArray (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    starGram (weightedArray A g) v = weightedGram (rowBare A g v) (fun a => g a.1 a.2) := by
  have hr : rowStar (weightedArray A g) v = vertexRoot g * rowBare A g v := by
    rw [rowStar_weightedArray, rowBare, Matrix.mul_assoc]
  rw [starGram, hr, Matrix.conjTranspose_mul, vertexRoot_star]
  unfold weightedGram
  calc
    _ = (rowBare A g v)ᴴ * (vertexRoot g * vertexRoot g) * rowBare A g v := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [vertexRoot_sq g hg]

lemma centerGram_weightedArray_padded (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    rowStar (weightedArray A g) v * (rowStar (weightedArray A g) v)ᴴ =
      weightedGram (colBare A g v) (fun a => g a.1 a.2) := by
  rw [rowStar_weightedArray]
  unfold colBare weightedGram
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, vertexRoot_star]
  rw [← vertexRoot_sq g hg]
  simp only [Matrix.mul_assoc]

lemma rowBare_congr (A : Three → Matrix ι ι ℂ) (g g' : Three → ι → ℝ) (v : Three)
    (he : ∀ w, w ≠ v → ∀ i, g' w i = g w i) : rowBare A g' v = rowBare A g v := by
  ext a b
  dsimp only [rowBare, vertexRoot]
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal, rowStar_apply]
  by_cases ha : a.1 = v
  · rw [ite_eq_left ha]
    by_cases hb : b.1 = v
    · rw [ha, hb, triangleBlocks_diag, Matrix.zero_apply, zero_mul, zero_mul]
    · rw [he b.1 hb]
  · rw [ite_eq_right ha, zero_mul, zero_mul]

lemma colBare_congr (A : Three → Matrix ι ι ℂ) (g g' : Three → ι → ℝ) (v : Three)
    (he : ∀ i, g' v i = g v i) : colBare A g' v = colBare A g v := by
  ext a b
  dsimp only [colBare, vertexRoot]
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
  simp only [Matrix.conjTranspose_apply, rowStar_apply]
  by_cases hb : b.1 = v
  · rw [ite_eq_left hb, hb, he]
  · rw [ite_eq_right hb, star_zero, zero_mul, zero_mul]

lemma rowStar_mul_adjoint (A : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar A v * (rowStar A v)ᴴ =
      blockD (fun w => if w = v then centerGram A v else 0) := by
  rw [rowStar_eq_blocks]
  let R : Matrix Three Three (Matrix ι ι ℂ) := fun a b => if a = v then triangleBlocks A a b else 0
  change blocks R * (blocks R)ᴴ = _
  rw [← blocks_star, ← blocks_mul]
  unfold blockD
  congr 1
  apply Matrix.ext
  intro a b
  change (∑ c, R a c * (R b c)ᴴ) = Matrix.diagonal (fun w => if w = v then centerGram A v else 0) a b
  dsimp only [R]
  by_cases ha : a = v <;> by_cases hb : b = v
  · subst a
    subst b
    simp only [ite_true, Matrix.diagonal_apply_eq]
    rfl
  · simp [ha, hb, Ne.symm hb]
  · simp [ha, hb]
  · simp only [ite_eq_right ha, zero_mul, Finset.sum_const_zero]
    by_cases hab : a = b
    · subst b
      rw [Matrix.diagonal_apply_eq, ite_eq_right ha]
    · rw [Matrix.diagonal_apply_ne _ hab]

end
end TriangularHilbert.MatrixEnergy
end

end OAI
