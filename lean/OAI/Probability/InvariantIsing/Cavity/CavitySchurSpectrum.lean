import OAI.Probability.InvariantIsing.Cavity.CavitySchurDeterminant
import OAI.Probability.InvariantIsing.Cavity.CavitySpecialBlocks

namespace OAI

/-! Resolvent compression for the actual finite repeated spectrum. The
complete special/cavity basis gives the Schur compression directly. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

private lemma cavity_complete_basis_gram {r d n : ℕ}
    (B : Matrix (Fin r) (Fin d) ℝ) (E : Matrix (Fin r) (Fin n) ℝ)
    (hB : B.transpose * B = 1) (hE : E.transpose * E = 1)
    (hBE : B.transpose * E = 0) :
    (Matrix.fromCols B E).transpose * Matrix.fromCols B E = 1 := by
  have hEB : E.transpose * B = 0 := by
    have h := congrArg Matrix.transpose hBE
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_zero] using h
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols,
    hB, hE, hBE, hEB, Matrix.fromBlocks_one]

private lemma cavity_complete_basis_blocks {r d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin d) ℝ)
    (E : Matrix (Fin r) (Fin n) ℝ) :
    (Matrix.fromCols B E).transpose * D * Matrix.fromCols B E =
      cavitySpecialBlocks D B E := by
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
  rfl

/-- The resolvent of the full special/cavity block is the same complete
orthogonal compression of the original spectral resolvent. -/
theorem cavity_complete_blocks_inverse {r d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin d) ℝ)
    (E : Matrix (Fin r) (Fin n) ℝ) (b : ℝ)
    (hB : B.transpose * B = 1) (hE : E.transpose * E = 1)
    (hBE : B.transpose * E = 0) (hcomplete : B * B.transpose + E * E.transpose = 1)
    (hD : IsUnit (b • (1 : Matrix (Fin r) (Fin r) ℝ) - D).det) :
    (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks D B E)⁻¹ = cavitySpecialBlocks (b • 1 - D)⁻¹ B E := by
  let Q := Matrix.fromCols B E
  have hQ : Q.transpose * Q = 1 := cavity_complete_basis_gram B E hB hE hBE
  have hQQ : Q * Q.transpose = 1 := by
    simpa only [Q, Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows] using hcomplete
  have hshift : b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks D B E = Q.transpose * (b • 1 - D) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hQ, cavity_complete_basis_blocks]
  rw [hshift, ← cavity_complete_basis_blocks]
  apply Matrix.inv_eq_right_inv
  calc
    (Q.transpose * (b • 1 - D) * Q) * (Q.transpose * (b • 1 - D)⁻¹ * Q) =
        Q.transpose * (b • 1 - D) * (Q * Q.transpose) * (b • 1 - D)⁻¹ * Q := by
      simp only [Matrix.mul_assoc]
    _ = Q.transpose * ((b • 1 - D) * (b • 1 - D)⁻¹) * Q := by
      rw [hQQ, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.mul_nonsing_inv _ hD, Matrix.mul_one, hQ]

private lemma cavityRepeatedSpectrum_shift {m n : ℕ} (lam : Fin m → ℝ) (b : ℝ) :
    b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam =
        Matrix.diagonal (fun i => b - lam (finProdFinEquiv.symm i).1) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [cavityRepeatedSpectrum]
  · simp [cavityRepeatedSpectrum, hij]

private lemma cavityRepeatedSpectrum_inverse_mul {m n : ℕ}
    (lam : Fin m → ℝ) (b : ℝ) (hb : ∀ a, b - lam a ≠ 0) :
    (b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam) *
        cavityRepeatedSpectrum (n := n) (fun a => (b - lam a)⁻¹) = 1 := by
  rw [cavityRepeatedSpectrum_shift]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [cavityRepeatedSpectrum, hb]
  · simp [cavityRepeatedSpectrum, hij]

lemma cavityRepeatedSpectrum_resolvent {m n : ℕ} (lam : Fin m → ℝ) (b : ℝ)
    (hb : ∀ a, b - lam a ≠ 0) :
    (b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam)⁻¹ =
        cavityRepeatedSpectrum (n := n) (fun a => (b - lam a)⁻¹) := by
  exact Matrix.inv_eq_right_inv (cavityRepeatedSpectrum_inverse_mul lam b hb)

/-- Exact `cav:compression`: the limiting cavity columns produce the
scalar finite-law Stieltjes transform, for every complete complement. -/
theorem cavity_limiting_blocks_compression {m d n : ℕ}
    (rho lam : Fin m → ℝ) (b : ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ)
    (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (hb : ∀ a, b - lam a ≠ 0) :
    ((b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks (cavityRepeatedSpectrum (n := n) lam) B
        (cavityLimitingStack (n := n) rho))⁻¹).toBlocks₂₂ =
      (∑ a, rho a / (b - lam a)) • 1 := by
  have hD := Matrix.isUnit_det_of_right_inverse
    (cavityRepeatedSpectrum_inverse_mul (n := n) lam b hb)
  rw [cavity_complete_blocks_inverse _ B _ b hB
    (cavityLimitingStack_gram rho hrho hsum) hBE hcomplete hD,
    cavityRepeatedSpectrum_resolvent lam b hb]
  change (cavityLimitingStack (n := n) rho).transpose *
    cavityRepeatedSpectrum (n := n) (fun a => (b - lam a)⁻¹) *
      cavityLimitingStack (n := n) rho = _
  simpa only [div_eq_mul_inv] using
    cavityLimitingStack_cavity_block rho (fun a => (b - lam a)⁻¹) hrho

end InvariantIsing

end

end OAI
