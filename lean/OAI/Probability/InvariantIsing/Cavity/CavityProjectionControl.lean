import OAI.Probability.InvariantIsing.Cavity.CavityCouplingAlgebra

namespace OAI

/-! Deterministic control of the special coordinates by the unnormalized
spectral images. Only the inverse square-root norms on the good event enter. -/

noncomputable section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_frame_transpose_contraction {r d : ℕ}
    (B : Matrix (Fin r) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (z : EuclideanSpace ℝ (Fin r)) :
    ‖(WithLp.toLp 2 (B.transpose *ᵥ z.ofLp) : EuclideanSpace ℝ (Fin d))‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  have ho : Orthonormal ℝ (fun i : Fin d =>
      (WithLp.toLp 2 (fun j : Fin r => B j i) : EuclideanSpace ℝ (Fin r))) := by
    rw [orthonormal_iff_ite]
    intro i j
    have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A i j) hB
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      PiLp.toLp_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      mul_comm] using h
  have hb := ho.sum_inner_products_le (s := Finset.univ) z
  simpa only [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial, PiLp.toLp_apply, Matrix.mulVec, Matrix.transpose_apply,
    Real.norm_eq_abs, sq_abs, mul_comm] using hb

lemma cavity_normalized_image_norm {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℝ) (z : EuclideanSpace ℝ (Fin r))
    {L : ℝ} (hL : 0 ≤ L) (hbound : ‖(CFC.sqrt (A.transpose * A))⁻¹‖ ≤ L) :
    ‖(WithLp.toLp 2 ((cavityNormalizeFrame A).transpose *ᵥ z.ofLp) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤
    L ^ 2 * ‖(WithLp.toLp 2 (A.transpose *ᵥ z.ofLp) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  let S := (CFC.sqrt (A.transpose * A))⁻¹
  have hSt : ‖S.transpose‖ ≤ L := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.l2_opNorm_conjTranspose S).le.trans hbound
  have hn := (Matrix.l2_opNorm_mulVec S.transpose
    (WithLp.toLp 2 (A.transpose *ᵥ z.ofLp) : EuclideanSpace ℝ (Fin n))).trans
    (mul_le_mul_of_nonneg_right hSt (norm_nonneg _))
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mpr hn
  simpa only [cavityNormalizeFrame, Matrix.transpose_mul, ← Matrix.mulVec_mulVec,
    mul_pow, S, EuclideanSpace.equiv, PiLp.coe_symm_continuousLinearEquiv] using hs

lemma cavity_eigenspace_projection_norm {r m n : ℕ}
    (A : Fin m → Matrix (Fin r) (Fin n) ℝ) (z : EuclideanSpace ℝ (Fin r)) :
    ‖(WithLp.toLp 2 ((cavityEigenspaceFrame A).transpose *ᵥ z.ofLp) :
      EuclideanSpace ℝ (Fin (m * n)))‖ ^ 2 =
    ∑ a, ‖(WithLp.toLp 2 ((cavityNormalizeFrame (A a)).transpose *ᵥ z.ofLp) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i : Fin (m * n), (∑ j : Fin r,
      cavityNormalizeFrame (A (finProdFinEquiv.symm i).1) j (finProdFinEquiv.symm i).2 * z j) ^ 2) =
    ∑ a, ∑ i : Fin n, (∑ j : Fin r, cavityNormalizeFrame (A a) j i * z j) ^ 2
  calc
    _ = ∑ t : Fin m × Fin n, (∑ j : Fin r,
        cavityNormalizeFrame (A t.1) j t.2 * z j) ^ 2 := by
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.sum_comp finProdFinEquiv
          (fun i : Fin (m * n) => (∑ j : Fin r,
            cavityNormalizeFrame (A (finProdFinEquiv.symm i).1) j
              (finProdFinEquiv.symm i).2 * z j) ^ 2)).symm
    _ = _ := Fintype.sum_prod_type _

theorem cavity_special_projection_control {r m n d : ℕ}
    (A : Fin m → Matrix (Fin r) (Fin n) ℝ)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (z : EuclideanSpace ℝ (Fin r)) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ a, ‖(CFC.sqrt ((A a).transpose * A a))⁻¹‖ ≤ L) :
    ‖(WithLp.toLp 2 ((cavityEigenspaceFrame A * B).transpose *ᵥ z.ofLp) :
      EuclideanSpace ℝ (Fin d))‖ ^ 2 ≤
    L ^ 2 * ∑ a, ‖(WithLp.toLp 2 ((A a).transpose *ᵥ z.ofLp) :
      EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
  apply (cavity_frame_transpose_contraction B hB
    (WithLp.toLp 2 ((cavityEigenspaceFrame A).transpose *ᵥ z.ofLp))).trans
  rw [cavity_eigenspace_projection_norm, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => cavity_normalized_image_norm (A a) z hL (hbound a)

end InvariantIsing

end

end OAI
