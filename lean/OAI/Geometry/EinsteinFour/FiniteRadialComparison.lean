import OAI.Geometry.EinsteinFour.ModeCompression
import OAI.Geometry.EinsteinFour.OrthogonalCompression

namespace OAI

/-! The finite determinant comparison before the mesh limit. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

theorem det_scalarLift {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) :
    (scalarLift G).det = G.det ^ 3 := by
  simpa only [scalarLift, Matrix.kronecker, Matrix.det_one, one_pow,
    Fintype.card_fin, one_mul] using Matrix.det_kronecker (1 : NormalMatrix) G

/-- Normalizing by a scalar comparison matrix divides the determinant by
the cube of its scalar determinant. -/
theorem det_normalized_matrix {N : ℕ}
    (G L : Matrix (Fin N) (Fin N) ℝ)
    (K : Matrix (Fin 3 × Fin N) (Fin 3 × Fin N) ℝ) (hG : G * L * G = 1) :
    (scalarLift G * K * scalarLift G).det = K.det / L.det ^ 3 := by
  have hd : G.det * L.det * G.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hG
  have hL : L.det ≠ 0 := by
    intro hz
    simp only [hz, mul_zero, zero_mul] at hd
    exact zero_ne_one hd
  have hg : G.det ^ 2 = 1 / L.det := by
    apply (eq_div_iff hL).mpr
    nlinarith [hd]
  rw [Matrix.det_mul, Matrix.det_mul, det_scalarLift]
  calc
    G.det ^ 3 * K.det * G.det ^ 3 = (G.det ^ 2) ^ 3 * K.det := by ring
    _ = K.det / L.det ^ 3 := by rw [hg]; ring

/-- The first scalar mode bounds the determinant of the normalized
Jacobi matrix. Positivity and the scalar eigenmode are explicit here;
the orthogonal completion and complementary trace estimate are proved. -/
theorem finite_normalized_radial_comparison {N : ℕ} (hN : 0 < N)
    (G L : Matrix (Fin N) (Fin N) ℝ) (A : Fin N → NormalMatrix)
    (w : Fin N → ℝ) (a g : ℝ)
    (hw : ∑ i, w i ^ 2 = 1) (hGsymm : Gᵀ = G) (hG : G * L * G = 1)
    (heigen : G *ᵥ w = g • w) (hA : ∀ i, (A i).trace = 0)
    (hpos : (scalarLift G * (scalarLift L - a ^ 2 • Matrix.blockDiagonal A) *
      scalarLift G).PosDef) :
    (scalarLift G * (scalarLift L - a ^ 2 • Matrix.blockDiagonal A) * scalarLift G).det ≤
      ((1 : NormalMatrix) - (a * g) ^ 2 • (∑ i, w i ^ 2 • A i)).det := by
  have hcomp := normalized_mode_compression G L A w a g hw hGsymm hG heigen
  have htrcomp : ((modeEmbedding w)ᴴ *
      (scalarLift G * (scalarLift L - a ^ 2 • Matrix.blockDiagonal A) * scalarLift G) *
      modeEmbedding w).trace = 3 := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hcomp, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.trace_sum]
    simp [Matrix.trace_smul, hA]
  have hcard : Fintype.card (Fin 3 × Fin N) =
      Fintype.card (Fin 3) + Fintype.card (Fin (3 * N - 3)) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  have hb := det_le_isometric_compression_of_card hcard (modeEmbedding w) hpos
    (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      modeEmbedding_orthonormal w hw)
    (by simpa using (normalized_jacobi_trace G L A a hG hA).le)
    (by simpa using htrcomp)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hcomp] using hb

end

end PositiveEinsteinFour.Jacobi

end OAI
