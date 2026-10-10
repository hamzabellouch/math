import OAI.Analysis.NumericalRange.ConformalWinding

namespace OAI

section

section
noncomputable section
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexConjugate InnerProductSpace
namespace CompleteCrouzeix

lemma eigenvalue_mem_numericalRange {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    {z : ℂ} {x : EuclideanSpace ℂ (Fin n)} (hx : x ≠ 0)
    (he : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x = z • x) :
    z ∈ numericalRange A := by
  let y := (‖x‖⁻¹ : ℝ) • x
  have hy : ‖y‖ = 1 := by simp [y, norm_smul, norm_ne_zero_iff.mpr hx]
  have he' : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A y = z • y := by
    simp [y, ContinuousLinearMap.map_smul_of_tower, he, smul_comm (‖x‖⁻¹ : ℝ) z]
  refine ⟨y, hy, ?_⟩
  rw [he', inner_smul_right, inner_self_eq_norm_sq_to_K, hy]
  simp

theorem spectrum_subset_numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    spectrum ℂ A ⊆ numericalRange A := by
  intro z hz
  have hz' : z ∈ spectrum ℂ A.toLin' := by simpa using hz
  obtain ⟨v,hv⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hz').exists_hasEigenvector
  let x : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v
  apply eigenvalue_mem_numericalRange (x := x)
  · simpa [x] using hv.2
  · change WithLp.toLp 2 (A.toLin' v) = z • WithLp.toLp 2 v
    rw [hv.apply_eq_smul]
    rfl

lemma isUnit_resolvent_of_not_mem_numericalRange {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} (hz : z ∉ numericalRange A) :
    IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ) - A) := by
  have hs : z ∉ spectrum ℂ A := fun h => hz (spectrum_subset_numericalRange A h)
  simpa only [spectrum, resolventSet, Set.mem_compl_iff, Set.mem_ofPred_eq,
    not_not, Algebra.algebraMap_eq_smul_one] using hs

lemma posSemidef_of_unit_quadratic {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.IsHermitian)
    (hq : ∀ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 →
      0 ≤ (inner ℂ x (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) H x)).re) :
    H.PosSemidef := by
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr hH, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx]
  let y := (‖x‖⁻¹ : ℝ) • x
  have hy : ‖y‖ = 1 := by simp [y, norm_smul, norm_ne_zero_iff.mpr hx]
  have hxy : x = (‖x‖ : ℝ) • y := by
    simp [y, smul_smul, norm_ne_zero_iff.mpr hx]
  have h := hq y hy
  rw [inner_re_symm]
  change 0 ≤ (inner ℂ x (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) H x)).re
  rw [hxy, ContinuousLinearMap.map_smul_of_tower]
  simp only [inner_smul_left_eq_star_smul, inner_smul_right_eq_smul, starRingEnd_apply, star_trivial, Complex.smul_re, smul_eq_mul]
  exact mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) h)

lemma supporting_form_posSemidef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {z N : ℂ}
    (hs : ∀ w ∈ numericalRange A, 0 ≤ (conj N * (z-w)).re) :
    (N • (z • (1 : Matrix (Fin n) (Fin n) ℂ)-A)ᴴ +
      conj N • (z • (1 : Matrix (Fin n) (Fin n) ℂ)-A)).PosSemidef := by
  let R := z • (1 : Matrix (Fin n) (Fin n) ℂ)-A
  apply posSemidef_of_unit_quadratic
  · change (N • Rᴴ + conj N • R).IsHermitian
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_conjTranspose, starRingEnd_apply, star_star]
    exact add_comm _ _
  · intro x hx
    let e := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
    have h := hs (inner ℂ x (e A x)) ⟨x,hx,rfl⟩
    have hr : inner ℂ x (e R x) = z-inner ℂ x (e A x) := by
      simp only [R, map_sub, map_smul, map_one, sub_apply,
        smul_apply, one_apply_eq_self,
        inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hx]
      simp
    change 0 ≤ (inner ℂ x (e (N • Rᴴ + conj N • R) x)).re
    have he : e Rᴴ = (e R).adjoint := map_star e R
    rw [map_add, map_smul, map_smul, add_apply,
      smul_apply, smul_apply,
      inner_add_right, inner_smul_right, inner_smul_right, he,
      ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm (e R x) x, hr]
    simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im] at *
    nlinarith

theorem supporting_resolvent_posSemidef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    {z N : ℂ} (hz : z ∉ numericalRange A)
    (hs : ∀ w ∈ numericalRange A, 0 ≤ (conj N * (z-w)).re) :
    (N • (z • (1 : Matrix (Fin n) (Fin n) ℂ)-A)⁻¹ +
      (N • (z • (1 : Matrix (Fin n) (Fin n) ℂ)-A)⁻¹)ᴴ).PosSemidef := by
  let R := z • (1 : Matrix (Fin n) (Fin n) ℂ)-A
  have hu : IsUnit R := isUnit_resolvent_of_not_mem_numericalRange hz
  have h := (supporting_form_posSemidef hs).conjTranspose_mul_mul_same R⁻¹
  have hR : R*R⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det R).mp hu)
  have hRi : R⁻¹*R = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det R).mp hu)
  have hh : R⁻¹ᴴ*(N • Rᴴ + conj N • R)*R⁻¹ = N • R⁻¹ + (N • R⁻¹)ᴴ := by
    simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R⁻¹ᴴ Rᴴ R⁻¹, ← Matrix.conjTranspose_mul, hR,
      Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    simp only [Matrix.conjTranspose_smul, starRingEnd_apply]
  exact hh ▸ h

end CompleteCrouzeix

end

end
end

end OAI
