import OAI.Analysis.TriangularHilbert.HeatStar

namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma hessianCost_zero_direction (P : Matrix ι ι ℂ) : hessianCost P 0 = 0 := by
  unfold hessianCost
  rw [rootCost_eq_of_solution (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P))
    (show sylv (CFC.sqrt P) 0 = 0 by simp [sylv])]
  simp [hsReal]

lemma hessianCost_singleBlock (P K : Matrix ι ι ℂ) (hP : P.PosSemidef) (v : Three)
    (hsol : ∃ Y, sylv (CFC.sqrt P) Y = K) :
    hessianCost (blockD (fun w => if w = v then P else 0))
      (blockD (fun w => if w = v then K else 0)) = hessianCost P K := by
  rw [hessianCost_blockD _ _ (fun w => by split_ifs; exact hP; exact Matrix.PosSemidef.zero)
    (fun w => by split_ifs; exact hsol; exact ⟨0, by simp [sylv]⟩)]
  apply (Finset.sum_eq_single v _ _).trans
  · simp only [ite_true]
  · intro w _ hw
    simp only [ite_eq_right hw, hessianCost_zero_direction]
  · simp

lemma rowStar_blockD_adjoint (W D : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar W v * blockD D * (rowStar W v)ᴴ =
      blockD (fun a => if a = v then
        ∑ w, triangleBlocks W v w * D w * (triangleBlocks W v w)ᴴ else 0) := by
  rw [rowStar_blocks]
  let R : Matrix Three Three (Matrix ι ι ℂ) := fun a b => if a = v then triangleBlocks W a b else 0
  change blocks R * blocks (Matrix.diagonal D) * (blocks R)ᴴ = _
  rw [← blocks_star, ← blocks_mul, ← blocks_mul]
  unfold blockD
  congr 1
  apply Matrix.ext
  intro a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose]
  change (∑ c, R a c * D c * (R b c)ᴴ) = _
  dsimp only [R]
  by_cases ha : a = v <;> by_cases hb : b = v
  · subst a
    subst b
    simp only [ite_true, Matrix.diagonal_apply_eq]
  · simp [ha, hb, Ne.symm hb]
  · simp [ha, hb]
  · simp only [ite_eq_right ha, zero_mul, Finset.sum_const_zero]
    by_cases hab : a = b
    · subst b
      rw [Matrix.diagonal_apply_eq, ite_eq_right ha]
    · rw [Matrix.diagonal_apply_ne _ hab]

lemma rowStar_singleBlock_adjoint (W : Three → Matrix ι ι ℂ) (L : Matrix ι ι ℂ)
    (v w : Three) :
    rowStar W v * blockD (fun a => if a = w then L else 0) * (rowStar W v)ᴴ =
      blockD (fun a => if a = v then triangleBlocks W v w * L * (triangleBlocks W v w)ᴴ else 0) := by
  rw [rowStar_blockD_adjoint]
  congr 1
  funext a
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma hessianCost_rowStar_singleBlock (W : Three → Matrix ι ι ℂ) (L : Matrix ι ι ℂ)
    (v w : Three) :
    hessianCost (rowStar W v * (rowStar W v)ᴴ)
      (rowStar W v * blockD (fun a => if a = w then L else 0) * (rowStar W v)ᴴ) =
      hessianCost (centerGram W v) ((triangleBlocks W w v)ᴴ * L * triangleBlocks W w v) := by
  rw [rowStar_mul_adjoint, rowStar_singleBlock_adjoint]
  have hsol := sylv_solvable_mono
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg ((triangleBlocks W w v)ᴴ * triangleBlocks W w v)))
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (centerGram W v))).isHermitian
    (sylv_solvable_inserted_gram (triangleBlocks W w v) L)
    (CFC.sqrt_le_sqrt _ _ (edgeGram_le_centerGram W v w))
  rw [← triangleBlocks_adj W w v, Matrix.conjTranspose_conjTranspose]
  exact hessianCost_singleBlock _ _ (centerGram_posSemidef W v) v hsol

lemma vertexRoot_insert (g d : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    vertexRoot g * blockD (fun v => Matrix.diagonal (fun i => (d v i : ℂ))) * vertexRoot g =
      Matrix.diagonal (fun a => (g a.1 a.2 * d a.1 a.2 : ℂ)) := by
  have hb : blockD (fun v => Matrix.diagonal (fun i => (d v i : ℂ))) =
      Matrix.diagonal (fun a => (d a.1 a.2 : ℂ)) := by
    ext ⟨v,i⟩ ⟨w,j⟩
    by_cases hv : v = w <;> by_cases hi : i = j <;> simp [blockD, blocks, Matrix.diagonal, hv, hi, Prod.mk.injEq]
  rw [hb, vertexRoot, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext ⟨v,i⟩
  rw [mul_comm (Real.sqrt _ : ℂ) (d v i), mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (hg v i)]
  push_cast
  ring

lemma rowBare_insert (A : Three → Matrix ι ι ℂ) (g d : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    weightedGram (rowBare A g v) (fun a => g a.1 a.2 * d a.1 a.2) =
      starInsert (weightedArray A g) (fun v => Matrix.diagonal (fun i => (d v i : ℂ))) v := by
  unfold starInsert
  rw [rowStar_weightedArray]
  unfold weightedGram rowBare
  simp only [Complex.ofReal_mul]
  rw [← vertexRoot_insert g d hg]
  simp only [Matrix.conjTranspose_mul, vertexRoot_star, Matrix.mul_assoc]

lemma colBare_insert (A : Three → Matrix ι ι ℂ) (g d : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) (v : Three) :
    weightedGram (colBare A g v) (fun a => g a.1 a.2 * d a.1 a.2) =
      rowStar (weightedArray A g) v *
        blockD (fun v => Matrix.diagonal (fun i => (d v i : ℂ))) *
        (rowStar (weightedArray A g) v)ᴴ := by
  rw [rowStar_weightedArray]
  unfold weightedGram colBare
  simp only [Complex.ofReal_mul]
  rw [← vertexRoot_insert g d hg]
  simp only [Matrix.conjTranspose_mul, vertexRoot_star, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

end
end TriangularHilbert.MatrixEnergy
end

end OAI
