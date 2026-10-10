import OAI.Probability.InvariantIsing.Cavity.CavitySchurSpectrum
import OAI.Probability.InvariantIsing.Spectral.SpectralCalculus

namespace OAI

/-! Exact multiplicities in the cavity Schur determinant and the finite
spectral inverse used to evaluate the scalar cavity field. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

private lemma cavity_complete_conjugate_det {r s : Type*} [Fintype r] [Fintype s]
    [DecidableEq r] [DecidableEq s]
    (X : Matrix r r ℝ) (Q : Matrix r s ℝ)
    (hQ : Q.transpose * Q = 1) (hQQ : Q * Q.transpose = 1) :
    (Q.transpose * X * Q).det = X.det := by
  have hleft : Q.transpose * X * Q = 1 + Q.transpose * ((X - 1) * Q) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, hQ]
    rw [← Matrix.mul_assoc]
    abel
  have hright : 1 + ((X - 1) * Q) * Q.transpose = X := by
    rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
    abel
  rw [hleft, Matrix.det_one_add_mul_comm, hright]

/-- Determinants are preserved by the complete special/cavity basis,
even though its two index types need not be definitionally equal. -/
theorem cavity_complete_blocks_determinant {r d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin d) ℝ)
    (E : Matrix (Fin r) (Fin n) ℝ) (b : ℝ)
    (hB : B.transpose * B = 1) (hE : E.transpose * E = 1)
    (hBE : B.transpose * E = 0) (hcomplete : B * B.transpose + E * E.transpose = 1) :
    (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks D B E).det =
        (b • (1 : Matrix (Fin r) (Fin r) ℝ) - D).det := by
  let Q := Matrix.fromCols B E
  have hEB : E.transpose * B = 0 := by
    have h := congrArg Matrix.transpose hBE
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h
  have hQ : Q.transpose * Q = 1 := by
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols,
      hB, hE, hBE, hEB, Matrix.fromBlocks_one]
  have hQQ : Q * Q.transpose = 1 := by
    simpa only [Q, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows] using hcomplete
  have hblock : Q.transpose * D * Q = cavitySpecialBlocks D B E := by
    rw [Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
    rfl
  have heq : b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks D B E = Q.transpose * (b • 1 - D) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hQ, hblock]
  rw [heq]
  exact cavity_complete_conjugate_det _ Q hQ hQQ

lemma cavityRepeatedSpectrum_shift_eq {m n : ℕ} (lam : Fin m → ℝ) (b : ℝ) :
    b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam =
        cavityRepeatedSpectrum (n := n) (fun a => b - lam a) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [cavityRepeatedSpectrum]
  · simp [cavityRepeatedSpectrum, hij]

/-- Every eigenvalue in the full limiting block occurs once for each
cavity coordinate. -/
theorem cavityRepeatedSpectrum_determinant {m n : ℕ} (lam : Fin m → ℝ) (b : ℝ) :
    (b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam).det = ∏ a, (b - lam a) ^ n := by
  rw [cavityRepeatedSpectrum_shift_eq, cavityRepeatedSpectrum, Matrix.det_diagonal]
  rw [← Equiv.prod_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.prod_prod_type, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem cavity_limiting_blocks_determinant {m d n : ℕ}
    (rho lam : Fin m → ℝ) (b : ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1) :
    (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks (cavityRepeatedSpectrum (n := n) lam) B
        (cavityLimitingStack (n := n) rho)).det = ∏ a, (b - lam a) ^ n := by
  rw [cavity_complete_blocks_determinant _ B _ b hB
    (cavityLimitingStack_gram rho hrho hsum) hBE hcomplete,
    cavityRepeatedSpectrum_determinant]

/-- The actual inverse-transform argument realizes the compression `x I`
without assuming a separate scalar resolvent identity. -/
theorem cavity_finiteInverse_blocks_compression {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (x : ℝ) (hx : 0 < x) :
    ((finiteInverse rho lam hrho hsum x •
        (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks (cavityRepeatedSpectrum (n := n) lam) B
        (cavityLimitingStack (n := n) rho))⁻¹).toBlocks₂₂ = x • 1 := by
  have hs := finiteInverse_spec rho lam hrho hsum hx
  rw [cavity_limiting_blocks_compression rho lam _ (fun a => (hrho a).le)
    hsum B hB hBE hcomplete (fun a => ne_of_gt (sub_pos.mpr (hs.1 a)))]
  exact congrArg (fun y : ℝ => y • (1 : Matrix (Fin n) (Fin n) ℝ)) hs.2

end InvariantIsing

end

end OAI
