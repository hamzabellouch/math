import OAI.Probability.InvariantIsing.Cavity.CavitySchurMultiplicity

namespace OAI

/-! The scalar Schur field of the actual limiting cavity block is the
finite spectral R-transform, including its prescribed value at zero. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

private lemma cavity_compressed_shift_posDef {r d : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin d) ℝ) (b : ℝ)
    (hB : B.transpose * B = 1) (hD : (b • (1 : Matrix (Fin r) (Fin r) ℝ) - D).PosDef) :
    (b • (1 : Matrix (Fin d) (Fin d) ℝ) - B.transpose * D * B).PosDef := by
  have hBinj : Function.Injective B.mulVec := by
    intro x y hxy
    have h := congrArg (fun z => B.transpose *ᵥ z) hxy
    simpa only [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec] using h
  have h := hD.conjTranspose_mul_mul_same hBinj
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hB] using h

private lemma cavitySpecialBlocks_symmetric_fromBlocks {r d n : ℕ}
    (D : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin d) ℝ)
    (E : Matrix (Fin r) (Fin n) ℝ) (hD : D.transpose = D) :
    cavitySpecialBlocks D B E = Matrix.fromBlocks (B.transpose * D * B)
      (B.transpose * D * E) (B.transpose * D * E).transpose (E.transpose * D * E) := by
  unfold cavitySpecialBlocks
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hD]
  simp only [Matrix.mul_assoc]

/-- The source field identity at its true finite-law inverse argument.
Both required determinant hypotheses are derived from spectral positivity. -/
theorem cavity_limiting_field_eq_finiteR {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (x : ℝ) (hx : 0 < x) :
    let D := cavityRepeatedSpectrum (n := n) lam
    let E := cavityLimitingStack (n := n) rho
    let b := finiteInverse rho lam hrho hsum x
    E.transpose * D * E + (B.transpose * D * E).transpose *
      (b • (1 : Matrix (Fin d) (Fin d) ℝ) - B.transpose * D * B)⁻¹ *
        (B.transpose * D * E) = finiteR rho lam hrho hsum x • 1 := by
  dsimp only
  let D := cavityRepeatedSpectrum (n := n) lam
  let E := cavityLimitingStack (n := n) rho
  let b := finiteInverse rho lam hrho hsum x
  let A := B.transpose * D * B
  let L := B.transpose * D * E
  let C := E.transpose * D * E
  have hb : ∀ a, lam a < b := (finiteInverse_spec rho lam hrho hsum hx).1
  have hDsym : D.transpose = D := Matrix.diagonal_transpose _
  have hD : (b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) - D).PosDef := by
    rw [show D = cavityRepeatedSpectrum (n := n) lam from rfl,
      cavityRepeatedSpectrum_shift_eq]
    exact Matrix.PosDef.diagonal (fun i => sub_pos.mpr (hb (finProdFinEquiv.symm i).1))
  have hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det :=
    isUnit_iff_ne_zero.mpr (cavity_compressed_shift_posDef D B b hB hD).det_pos.ne'
  have hblocks : Matrix.fromBlocks A L L.transpose C = cavitySpecialBlocks D B E :=
    (cavitySpecialBlocks_symmetric_fromBlocks D B E hDsym).symm
  have hM : IsUnit (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C).det := by
    rw [hblocks]
    change IsUnit (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      cavitySpecialBlocks (cavityRepeatedSpectrum (n := n) lam) B
        (cavityLimitingStack (n := n) rho)).det
    rw [cavity_limiting_blocks_determinant rho lam b (fun a => (hrho a).le)
      hsum B hB hBE hcomplete]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
      (fun a _ => pow_ne_zero n (ne_of_gt (sub_pos.mpr (hb a)))))
  have hcomp : ((b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C)⁻¹).toBlocks₂₂ = x • 1 := by
    rw [hblocks]
    exact cavity_finiteInverse_blocks_compression rho lam hrho hsum B hB hBE hcomplete x hx
  have hf := cavity_schur_scalar_field A L C b x hx.ne' hA hM hcomp
  simpa only [finiteR, ite_eq_left hx, one_div, A, L, C, D, E, b] using hf

theorem cavity_limiting_cavityBlock_eq_finiteR_zero {m n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) :
    (cavityLimitingStack (n := n) rho).transpose * cavityRepeatedSpectrum (n := n) lam *
      cavityLimitingStack (n := n) rho = finiteR rho lam hrho hsum 0 • 1 := by
  simpa only [finiteR, lt_self_iff_false, ite_false] using
    cavityLimitingStack_cavity_block rho lam (fun a => (hrho a).le)

end InvariantIsing

end

end OAI
