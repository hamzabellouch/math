import OAI.Probability.InvariantIsing.Cavity.CavityResolvent

namespace OAI

/-! The finite Schur-complement evaluation in `cav:compression` and
`cav:scalar-field`. All block inverses are ordinary nonsingular inverses. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

private lemma cavity_block_inverse_bottom {d n : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin d) ℝ) (D : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det) (hM : IsUnit (Matrix.fromBlocks A B C D).det) :
    ((Matrix.fromBlocks A B C D)⁻¹).toBlocks₂₂ = (D - C * A⁻¹ * B)⁻¹ := by
  let := Matrix.invertibleOfIsUnitDet A hA
  let := Matrix.invertibleOfIsUnitDet (Matrix.fromBlocks A B C D) hM
  let := Matrix.invertibleOfFromBlocks₁₁Invertible A B C D
  simpa only [Matrix.invOf_eq_nonsing_inv, Matrix.toBlocks_fromBlocks₂₂] using
    congrArg Matrix.toBlocks₂₂ (Matrix.invOf_fromBlocks₁₁_eq A B C D)

lemma cavity_block_shift {d n : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (b : ℝ) :
    b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
        Matrix.fromBlocks A L L.transpose C =
      Matrix.fromBlocks (b • 1 - A) (-L) (-L.transpose) (b • 1 - C) := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.one_apply, Matrix.fromBlocks, Matrix.smul_apply]

/-- Compressing the full resolvent onto the cavity block gives the inverse
of the Schur complement; no commutation of the special blocks is needed. -/
theorem cavity_schur_resolvent_compression {d n : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (b : ℝ)
    (hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det)
    (hM : IsUnit (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C).det) :
    ((b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C)⁻¹).toBlocks₂₂ =
        (b • 1 - C - L.transpose * (b • 1 - A)⁻¹ * L)⁻¹ := by
  rw [cavity_block_shift] at hM ⊢
  simpa only [Matrix.neg_mul, Matrix.mul_neg, neg_neg] using
    cavity_block_inverse_bottom (b • 1 - A) (-L) (-L.transpose) (b • 1 - C) hA hM

/-- The scalar compression `x I` forces the cavity field to be
`(b - 1/x) I`, the finite identity `cav:scalar-field`. -/
theorem cavity_schur_scalar_field {d n : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (b x : ℝ) (hx : x ≠ 0)
    (hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det)
    (hM : IsUnit (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C).det)
    (hcompression : ((b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C)⁻¹).toBlocks₂₂ = x • 1) :
    C + L.transpose * (b • 1 - A)⁻¹ * L = (b - x⁻¹) • 1 := by
  let D := b • (1 : Matrix (Fin d) (Fin d) ℝ) - A
  let E := b • (1 : Matrix (Fin n) (Fin n) ℝ) - C
  let := Matrix.invertibleOfIsUnitDet D hA
  have hMD : IsUnit (Matrix.fromBlocks D (-L) (-L.transpose) E).det := by
    simpa only [D, E, cavity_block_shift] using hM
  let := Matrix.invertibleOfIsUnitDet (Matrix.fromBlocks D (-L) (-L.transpose) E) hMD
  let := Matrix.invertibleOfFromBlocks₁₁Invertible D (-L) (-L.transpose) E
  have hS : IsUnit (b • (1 : Matrix (Fin n) (Fin n) ℝ) - C -
      L.transpose * (b • 1 - A)⁻¹ * L).det := by
    simpa only [D, E, Matrix.invOf_eq_nonsing_inv, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg] using
        Matrix.isUnit_det_of_invertible (E - (-L.transpose) * ⅟D * (-L))
  let := Matrix.invertibleOfIsUnitDet _ hS
  have hi : (b • (1 : Matrix (Fin n) (Fin n) ℝ) - C -
      L.transpose * (b • 1 - A)⁻¹ * L)⁻¹ = x • 1 := by
    rw [← cavity_schur_resolvent_compression A L C b hA hM]
    exact hcompression
  have hscalar : (x • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ = x⁻¹ • 1 := by
    apply Matrix.inv_eq_right_inv
    simp only [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, smul_smul,
      inv_mul_cancel₀ hx, one_smul]
  have hs := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹) hi
  rw [Matrix.inv_inv_of_invertible, hscalar] at hs
  rw [sub_smul]
  calc
    C + L.transpose * (b • 1 - A)⁻¹ * L =
        b • 1 - (b • 1 - C - L.transpose * (b • 1 - A)⁻¹ * L) := by abel
    _ = b • 1 - x⁻¹ • 1 := by rw [hs]

/-- Inserting the already proved quadratic resolvent transform gives the
same scalar cavity field expressed in the original covariance. -/
theorem cavity_schur_tilted_field {d n : ℕ}
    (A A₀ : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (b x : ℝ) (hx : x ≠ 0)
    (hA₀ : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀).det)
    (hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det)
    (hM : IsUnit (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C).det)
    (hcompression : ((b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C)⁻¹).toBlocks₂₂ = x • 1) :
    C + L.transpose * cavityResolvent (A - A₀) (b • 1 - A₀)⁻¹ * L =
      (b - x⁻¹) • 1 := by
  rw [cavityResolvent_spectral_transform A A₀ b hA₀ hA]
  exact cavity_schur_scalar_field A L C b x hx hA hM hcompression

end InvariantIsing

end

end OAI
