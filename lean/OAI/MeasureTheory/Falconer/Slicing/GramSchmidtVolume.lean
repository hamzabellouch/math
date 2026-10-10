import OAI.MeasureTheory.Falconer.Slicing.GramSchmidtSlab

namespace OAI

/-! # The Gram volume is the product of successive residual lengths -/

namespace Falconer
open InnerProductSpace
open scoped BigOperators Matrix
variable {d : ℕ}

theorem gram_volume_eq_abs_basis_det (b : OrthonormalBasis (Fin d) ℝ (Space d))
    (v : Fin d → Space d) :
    Real.sqrt (Matrix.gram ℝ v).det = |b.toBasis.det v| := by
  rw [Matrix.gram_eq_conjTranspose_mul b v, Matrix.det_mul, Matrix.det_conjTranspose]
  change Real.sqrt ((b.toBasis.det v)*(b.toBasis.det v)) = _
  rw [← pow_two, Real.sqrt_sq_eq_abs]

theorem gramSchmidt_basis_diagonal_abs (v : Fin d → Space d) (i : Fin d) :
    |inner ℝ (gramSchmidtOrthonormalBasis
      (show Module.finrank ℝ (Space d) = Fintype.card (Fin d) by simp) v i) (v i)| =
      ‖gramSchmidt ℝ v i‖ := by
  let w := gramSchmidt ℝ v i
  have he : inner ℝ w (v i) = ‖w‖^2 := by
    have hh := inner_gramSchmidt_of_prefix_orthogonal w v i
      (fun j hj => gramSchmidt_inv_triangular ℝ v hj)
    rw [← hh,real_inner_self_eq_norm_sq]
  by_cases hw : w = 0
  · have hz : gramSchmidtNormed ℝ v i = 0 := by
      simp [gramSchmidtNormed, show gramSchmidt ℝ v i = 0 from hw]
    rw [inner_gramSchmidtOrthonormalBasis_eq_zero _ hz]
    change |(0:ℝ)| = ‖w‖
    simp only [hw,abs_zero,norm_zero]
  · have hz : gramSchmidtNormed ℝ v i ≠ 0 := by
      simp only [gramSchmidtNormed]
      exact smul_ne_zero (inv_ne_zero (by exact_mod_cast (norm_ne_zero_iff.mpr hw))) hw
    rw [gramSchmidtOrthonormalBasis_apply _ hz]
    change |inner ℝ (‖w‖⁻¹ • w) (v i)| = ‖w‖
    rw [real_inner_smul_left,he,pow_two,← mul_assoc,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw),one_mul,abs_of_nonneg (norm_nonneg w)]

theorem gram_volume_eq_residual_product (v : Fin d → Space d) :
    Real.sqrt (Matrix.gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ := by
  let b := gramSchmidtOrthonormalBasis
    (show Module.finrank ℝ (Space d) = Fintype.card (Fin d) by simp) v
  rw [gram_volume_eq_abs_basis_det b v]
  change |(gramSchmidtOrthonormalBasis _ v).toBasis.det v| = _
  rw [gramSchmidtOrthonormalBasis_det,Finset.abs_prod]
  exact Finset.prod_congr rfl (fun i _ => gramSchmidt_basis_diagonal_abs v i)

theorem small_gram_volume_has_small_residual (v : Fin d → Space d) {r : ℝ}
    (hr : 0 ≤ r) (h : Real.sqrt (Matrix.gram ℝ v).det < r^d) :
    ∃ i, ‖gramSchmidt ℝ v i‖ < r := by
  by_contra! hn
  have hlower : r^d ≤ Real.sqrt (Matrix.gram ℝ v).det := by
    rw [gram_volume_eq_residual_product]
    calc
      r^d = ∏ _i : Fin d, r := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hr) (fun i _ => hn i)
  exact (not_lt_of_ge hlower) h

end Falconer

end OAI
