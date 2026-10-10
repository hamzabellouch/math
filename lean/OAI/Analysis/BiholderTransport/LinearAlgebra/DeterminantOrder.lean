import Mathlib

namespace OAI

section
section
noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

namespace WeakMTWTransport

open Matrix
open scoped MatrixOrder

section DeterminantOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma det_one_add_posSemidef_ge_one {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    1 ≤ (1 + A).det := by
  have hspec := hA.isHermitian.spectral_theorem
  let U := hA.isHermitian.eigenvectorUnitary
  have hconj : (1 + A) =
      Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) U
        (Matrix.diagonal (fun i => 1 + hA.isHermitian.eigenvalues i)) := by
    rw [show Matrix.diagonal (fun i => 1 + hA.isHermitian.eigenvalues i) =
      1 + Matrix.diagonal hA.isHermitian.eigenvalues by
        rw [← Matrix.diagonal_one, ← Matrix.diagonal_add]]
    simp only [map_add, map_one]
    congr 1
  rw [hconj, Unitary.conjStarAlgAut_apply]
  have hu : (U : Matrix n n ℝ) * star (U : Matrix n n ℝ) = 1 := by
    exact Unitary.coe_mul_star_self U
  have hdetu : (U : Matrix n n ℝ).det * (star (U : Matrix n n ℝ)).det = 1 := by
    rw [← Matrix.det_mul, hu, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, hdetu, one_mul,
    Matrix.det_diagonal]
  exact Finset.one_le_prod₀ (fun eigenIndex _ => by
    linarith [hA.eigenvalues_nonneg eigenIndex])

lemma det_le_of_posDef_le {A B : Matrix n n ℝ} (hA : A.PosDef) (hAB : A ≤ B) :
    A.det ≤ B.det := by
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  have hRdet : R.det ≠ 0 := by
    have heq : A.det = R.det * R.det := by
      rw [hR, Matrix.det_mul]
      simp only [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, star_trivial]
    intro hz
    rw [hz, zero_mul] at heq
    exact hA.det_pos.ne' heq
  have hRi : IsUnit R.det := isUnit_iff_ne_zero.mpr hRdet
  let S := R⁻¹
  have hrs : R * S = 1 := R.mul_nonsing_inv hRi
  have hnorm : star S * A * S = 1 := by
    rw [hR]
    calc
      star S * (star R * R) * S = star (R * S) * (R * S) := by
        simp only [star_mul]; noncomm_ring
      _ = 1 := by rw [hrs]; simp
  have hD : (star S * (B - A) * S).PosSemidef :=
    hAB.conjTranspose_mul_mul_same S
  have hbound := det_one_add_posSemidef_ge_one hD
  have heq : 1 + star S * (B - A) * S = star S * B * S := by
    rw [← hnorm]
    noncomm_ring
  rw [heq] at hbound
  have hanorm := congrArg Matrix.det hnorm
  simp only [Matrix.det_mul, Matrix.star_eq_conjTranspose,
    Matrix.det_conjTranspose, star_trivial, Matrix.det_one] at hanorm hbound
  nlinarith [hA.det_pos]

lemma det_one_add_vecMulVec (u v : n → ℝ) :
    (1 + Matrix.vecMulVec u v).det = 1 + v ⬝ᵥ u := by
  have heq : Matrix.vecMulVec u v =
      Matrix.replicateCol Unit u * Matrix.replicateRow Unit v := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  rw [heq, Matrix.det_one_add_replicateCol_mul_replicateRow]

omit [DecidableEq n] in
lemma congruence_rank_one (S : Matrix n n ℝ) (p : n → ℝ) :
    Sᵀ * Matrix.vecMulVec p p * S =
      Matrix.vecMulVec (Sᵀ *ᵥ p) (Sᵀ *ᵥ p) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mulVec_transpose S p]

lemma oblique_fixes_kernel_form {L : Matrix n n ℝ} (hL : L.IsHermitian)
    {e : n → ℝ} (he : L *ᵥ e = 0) (a : n → ℝ) :
    (1 + Matrix.vecMulVec e a)ᵀ * L * (1 + Matrix.vecMulVec e a) = L := by
  have htr : Lᵀ = L := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hL.eq
  have hleft : (1 + Matrix.vecMulVec e a)ᵀ * L = L := by
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_vecMulVec,
      Matrix.add_mul, Matrix.one_mul, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose,
      htr, he, Matrix.vecMulVec_zero, add_zero]
  rw [hleft, Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, he,
    Matrix.zero_vecMulVec, add_zero]

omit [DecidableEq n] in

lemma transpose_congruence_mono {A B : Matrix n n ℝ} (hAB : A ≤ B)
    (S : Matrix n n ℝ) : Sᵀ * A * S ≤ Sᵀ * B * S := by
  have h := hAB.conjTranspose_mul_mul_same S
  rw [Matrix.le_iff]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
    Matrix.sub_mul] using h
end DeterminantOrder

end WeakMTWTransport
end
end
end

end OAI
