import OAI.Probability.InvariantIsing.Cavity.CavitySchurEvaluation

namespace OAI

/-! Determinant identities accompanying the cavity scalar-field
evaluation. The scalar compression supplies the exact Schur factor. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavity_schur_determinant {d n : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (b : ℝ)
    (hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det) :
    (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C).det =
      (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det *
        (b • (1 : Matrix (Fin n) (Fin n) ℝ) - C -
          L.transpose * (b • 1 - A)⁻¹ * L).det := by
  let := Matrix.invertibleOfIsUnitDet (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A) hA
  rw [cavity_block_shift]
  simpa only [Matrix.invOf_eq_nonsing_inv, Matrix.neg_mul,
    Matrix.mul_neg, neg_neg] using
      Matrix.det_fromBlocks₁₁ (b • 1 - A) (-L) (-L.transpose) (b • 1 - C)

/-- The `x^n` Schur factor in `cav:determinant`, before evaluating
the characteristic polynomial of the full repeated spectrum. -/
theorem cavity_schur_det_of_scalar_compression {d n : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (b x : ℝ) (hx : x ≠ 0)
    (hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det)
    (hM : IsUnit (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C).det)
    (hcompression : ((b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C)⁻¹).toBlocks₂₂ = x • 1) :
    (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det =
      x ^ n * (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
        Matrix.fromBlocks A L L.transpose C).det := by
  have hfield := cavity_schur_scalar_field A L C b x hx hA hM hcompression
  have hschur : b • (1 : Matrix (Fin n) (Fin n) ℝ) - C -
      L.transpose * (b • 1 - A)⁻¹ * L = x⁻¹ • 1 := by
    rw [sub_smul] at hfield
    calc
      _ = b • 1 - (C + L.transpose * (b • 1 - A)⁻¹ * L) := by abel
      _ = x⁻¹ • 1 := by rw [hfield]; abel
  rw [cavity_schur_determinant A L C b hA, hschur, Matrix.det_smul,
    Matrix.det_one, mul_one, Fintype.card_fin]
  symm
  calc
    _ = (x ^ n * (x⁻¹) ^ n) * (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det := by ring
    _ = _ := by rw [← mul_pow, mul_inv_cancel₀ hx, one_pow, one_mul]

/-- The first equality of `cav:determinant`, valid without commuting
`A` and `A₀`. -/
theorem cavity_tilt_determinant_ratio {d : ℕ}
    (A A₀ : Matrix (Fin d) (Fin d) ℝ) (b : ℝ)
    (hA₀ : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀).det) :
    (1 - (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀)⁻¹ * (A - A₀)).det =
      (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det /
        (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀).det := by
  have hfactor : 1 - (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀)⁻¹ * (A - A₀) =
      (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀)⁻¹ * (b • 1 - A) := by
    calc
      _ = (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀)⁻¹ * (b • 1 - A₀) -
          (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀)⁻¹ * (A - A₀) := by
        rw [Matrix.nonsing_inv_mul _ hA₀]
      _ = _ := by noncomm_ring
  apply (eq_div_iff hA₀.ne_zero).2
  rw [hfactor, Matrix.det_mul]
  calc
    _ = (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det *
        ((b • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀)⁻¹.det *
          (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀).det) := by ring
    _ = _ := by rw [Matrix.det_nonsing_inv_mul_det _ hA₀, mul_one]

end InvariantIsing

end

end OAI
