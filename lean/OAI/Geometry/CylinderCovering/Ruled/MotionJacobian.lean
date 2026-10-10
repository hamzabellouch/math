import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section
open Set MeasureTheory
namespace RuledApproximation.HyperbolicMotionJacobian

theorem plane_det_id_add_smul (A : Plane →ₗ[ℝ] Plane) (s : ℝ) :
    LinearMap.det (LinearMap.id + s • A) =
      1 + s * LinearMap.trace ℝ Plane A + s ^ 2 * LinearMap.det A := by
  let b := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  rw [← LinearMap.det_toMatrix b,
    LinearMap.trace_eq_matrix_trace ℝ b, ← LinearMap.det_toMatrix b A]
  simp only [map_add, map_smul, LinearMap.toMatrix_id, Matrix.det_fin_two,
    Matrix.trace_fin_two, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, smul_eq_mul]
  ring

theorem trace_det_of_opposite_eigenvalues (A : Plane →ₗ[ℝ] Plane)
    {lam : ℝ} (hlam : lam ≠ 0)
    (hp : Module.End.HasEigenvalue A lam)
    (hm : Module.End.HasEigenvalue A (-lam)) :
    LinearMap.trace ℝ Plane A = 0 ∧ LinearMap.det A = -(lam ^ 2) := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Polynomial.IsRoot,
    plane_charpoly] at hp hm
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C] at hp hm
  have hz : LinearMap.trace ℝ Plane A * lam = 0 := by nlinarith
  have ht : LinearMap.trace ℝ Plane A = 0 := (mul_eq_zero.mp hz).resolve_right hlam
  refine ⟨ht, ?_⟩
  rw [ht] at hp
  nlinarith

theorem deformation_det (A : Plane →ₗ[ℝ] Plane) {lam : ℝ} (hlam : lam ≠ 0)
    (hp : Module.End.HasEigenvalue A lam)
    (hm : Module.End.HasEigenvalue A (-lam)) (s : ℝ) :
    LinearMap.det (LinearMap.id + s • A) = 1 - s ^ 2 * lam ^ 2 := by
  obtain ⟨ht, hd⟩ := trace_det_of_opposite_eigenvalues A hlam hp hm
  rw [plane_det_id_add_smul, ht, hd]
  ring

theorem deformation_volume (A : Plane →ₗ[ℝ] Plane) {lam : ℝ} (hlam : lam ≠ 0)
    (hp : Module.End.HasEigenvalue A lam)
    (hm : Module.End.HasEigenvalue A (-lam)) (s : ℝ) (D : Set Plane) :
    volume ((fun p => p + s • A p) '' D) =
      ENNReal.ofReal |1 - s ^ 2 * lam ^ 2| * volume D := by
  have h := volume.addHaar_image_linearMap (LinearMap.id + s • A) D
  rw [deformation_det A hlam hp hm] at h
  exact h

theorem deformation_det_bounds (A : Plane →ₗ[ℝ] Plane) {lam L s : ℝ}
    (_hL : 0 < L) (hlam : 0 < lam) (hsmall : L * lam < 1)
    (hp : Module.End.HasEigenvalue A lam)
    (hm : Module.End.HasEigenvalue A (-lam)) (hs : |s| ≤ L) :
    0 < LinearMap.det (LinearMap.id + s • A) ∧
      LinearMap.det (LinearMap.id + s • A) ≤ 1 ∧
      (LinearMap.det (LinearMap.id + s • A) = 1 ↔ s = 0) := by
  rw [deformation_det A hlam.ne' hp hm]
  have ha : |s * lam| < 1 := by
    rw [abs_mul, abs_of_pos hlam]
    exact (mul_le_mul_of_nonneg_right hs hlam.le).trans_lt hsmall
  have hsq : s ^ 2 * lam ^ 2 < 1 := by
    nlinarith [sq_abs (s * lam), abs_nonneg (s * lam)]
  refine ⟨by linarith, by nlinarith [mul_nonneg (sq_nonneg s) (sq_nonneg lam)], ?_⟩
  constructor
  · intro heq
    have hz : s ^ 2 * lam ^ 2 = 0 := by linarith
    have hz2 := (mul_eq_zero.mp hz).resolve_right (pow_ne_zero 2 hlam.ne')
    nlinarith [hz2]
  · rintro rfl
    simp

end RuledApproximation.HyperbolicMotionJacobian

end

end OAI
