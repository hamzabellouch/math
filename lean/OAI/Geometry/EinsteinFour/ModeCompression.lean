import OAI.Geometry.EinsteinFour.JacobiCompression

namespace OAI

/-! Compression onto a common scalar time mode in the three normal directions. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

def modeEmbedding {N : ℕ} (w : Fin N → ℝ) : Matrix (Fin 3 × Fin N) (Fin 3) ℝ :=
  fun i a => if i.1 = a then w i.2 else 0

theorem mul_modeEmbedding {N : ℕ}
    (M : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ)
    (w : Fin N → ℝ) (a b : Fin 3) (i : Fin N) :
    (M * modeEmbedding w) (a, i) b = ∑ j, blockAt M i j a b * w j := by
  simp [Matrix.mul_apply, modeEmbedding, Fintype.sum_prod_type, blockAt]

theorem mode_compression_apply {N : ℕ}
    (M : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ)
    (w : Fin N → ℝ) (a b : Fin 3) :
    ((modeEmbedding w)ᵀ * M * modeEmbedding w) a b =
      ∑ i, ∑ j, w i * w j * blockAt M i j a b := by
  rw [Matrix.mul_assoc]
  calc
    _ = ∑ i, w i * (M * modeEmbedding w) (a, i) b := by
      change (∑ k, (modeEmbedding w) k a * (M * modeEmbedding w) k b) = _
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp [modeEmbedding]
    _ = _ := by
      simp_rw [mul_modeEmbedding, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem mode_compression_diagonal {N : ℕ} (A : Fin N → NormalMatrix)
    (w : Fin N → ℝ) :
    (modeEmbedding w)ᵀ * Matrix.blockDiagonal A * modeEmbedding w =
      ∑ i, w i ^ 2 • A i := by
  ext a b
  rw [mode_compression_apply]
  simp only [blockAt_diagonal, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Matrix.ite_apply, Matrix.zero_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  funext i
  ring

theorem mode_compression_scalar {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (w : Fin N → ℝ) :
    (modeEmbedding w)ᵀ * scalarLift G * modeEmbedding w =
      (∑ i, ∑ j, w i * G i j * w j) • (1 : NormalMatrix) := by
  ext a b
  rw [mode_compression_apply]
  simp only [blockAt_scalarLift, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  congr 1
  funext i
  congr 1
  funext j
  ring

/-- Every unit time mode yields three orthonormal columns. -/
theorem modeEmbedding_orthonormal {N : ℕ} (w : Fin N → ℝ)
    (hw : ∑ i, w i ^ 2 = 1) :
    (modeEmbedding w)ᵀ * modeEmbedding w = 1 := by
  have h := mode_compression_scalar (1 : Matrix (Fin N) (Fin N) ℝ) w
  rw [scalarLift_one, Matrix.mul_one] at h
  simpa [Matrix.one_apply, mul_ite, mul_zero, ← pow_two, hw] using h

/-- Trace-free Weyl blocks give a trace-free compressed perturbation. -/
theorem trace_mode_compression_defect {N : ℕ} (A : Fin N → NormalMatrix)
    (w : Fin N → ℝ) (hA : ∀ i, (A i).trace = 0) :
    ((modeEmbedding w)ᵀ * Matrix.blockDiagonal A * modeEmbedding w).trace = 0 := by
  rw [mode_compression_diagonal, Matrix.trace_sum]
  simp [Matrix.trace_smul, hA]

theorem scalarLift_mode_eigenvector {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (w : Fin N → ℝ) (g : ℝ) (heigen : G *ᵥ w = g • w) :
    scalarLift G * modeEmbedding w = g • modeEmbedding w := by
  ext ⟨a, i⟩ b
  rw [mul_modeEmbedding]
  simp only [blockAt_scalarLift, Matrix.smul_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst b
    simpa [modeEmbedding, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.smul_apply,
      smul_eq_mul] using congrFun heigen i
  · simp [modeEmbedding, hab]

/-- The first-mode block of the normalized Jacobi matrix is exactly the
weighted curvature average. -/
theorem normalized_mode_compression {N : ℕ}
    (G L : Matrix (Fin N) (Fin N) ℝ) (A : Fin N → NormalMatrix)
    (w : Fin N → ℝ) (a g : ℝ)
    (hw : ∑ i, w i ^ 2 = 1) (hGsymm : Gᵀ = G) (hG : G * L * G = 1)
    (heigen : G *ᵥ w = g • w) :
    (modeEmbedding w)ᵀ *
        (scalarLift G * (scalarLift L - a ^ 2 • Matrix.blockDiagonal A) * scalarLift G) *
        modeEmbedding w =
      (1 : NormalMatrix) - (a * g) ^ 2 • (∑ i, w i ^ 2 • A i) := by
  have hLift : (scalarLift G)ᵀ = scalarLift G := by
    ext ⟨a, i⟩ ⟨b, j⟩
    change (1 : NormalMatrix) b a * G j i = (1 : NormalMatrix) a b * G i j
    rw [show G j i = G i j from congrFun (congrFun hGsymm i) j]
    simp only [Matrix.one_apply, eq_comm]
  have hright := scalarLift_mode_eigenvector G w g heigen
  have hleft : (modeEmbedding w)ᵀ * scalarLift G = g • (modeEmbedding w)ᵀ := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_smul, hLift] using
      congrArg Matrix.transpose hright
  have hbase : scalarLift G * scalarLift L * scalarLift G = 1 := by
    rw [← scalarLift_mul, ← scalarLift_mul, hG, scalarLift_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, hbase, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, modeEmbedding_orthonormal w hw]
  have hdefect : (modeEmbedding w)ᵀ *
        (scalarLift G * (a ^ 2 • Matrix.blockDiagonal A) * scalarLift G) * modeEmbedding w =
      (a * g) ^ 2 • (∑ i, w i ^ 2 • A i) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hleft]
    rw [Matrix.mul_assoc ((g • (modeEmbedding w)ᵀ) * (a ^ 2 • Matrix.blockDiagonal A)),
      hright]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mode_compression_diagonal]
    congr 1
    ring
  rw [hdefect]

end

end PositiveEinsteinFour.Jacobi

end OAI
