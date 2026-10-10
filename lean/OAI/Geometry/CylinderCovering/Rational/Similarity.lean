import OAI.Geometry.CylinderCovering.Rational.SimilarityDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Pointwise
namespace RationalSimilarity

lemma h_pos : 0 < h := by unfold h; positivity
lemma ell_pos : 0 < ell := by unfold ell; positivity
lemma h_ne_zero : h ≠ 0 := ne_of_gt h_pos
lemma ell_ne_zero : ell ≠ 0 := ne_of_gt ell_pos
lemma h_sq : h ^ 2 = 1 / 2 := by
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  unfold h
  rw [div_pow, hs]
  norm_num
lemma ell_eq : ell = h / 2 := by unfold ell h; ring
lemma ell_sq : ell ^ 2 = 1 / 8 := by rw [ell_eq, div_pow, h_sq]; norm_num
lemma ell_mul_h : ell * h = 1 / 4 := by rw [ell_eq]; nlinarith [h_sq]

@[simp] lemma phi_apply_zero (z : Space) : phi z 0 = -ell * z 0 := rfl
@[simp] lemma phi_apply_one (z : Space) : phi z 1 = ell * z 1 := rfl
@[simp] lemma phi_apply_two (z : Space) : phi z 2 = ell * (1 - z 2) := rfl

lemma phi_decomposition (z : Space) :
    phi z = ell • (reflection z + !₂[0, 0, 1]) := by
  ext i
  fin_cases i <;> simp [phi, reflection]
  ring

lemma reflection_isometry : Isometry reflection := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, reflection]
  ring

lemma phi_dist (x y : Space) : dist (phi x) (phi y) = ell * dist x y := by
  rw [phi_decomposition, phi_decomposition, dist_smul₀]
  rw [Real.norm_eq_abs, abs_of_pos ell_pos, dist_add_right]
  rw [reflection_isometry.dist_eq]

lemma phi_membership (z : Space) :
    phi z ∈ centeredTetrahedron ↔ z ∈ uncenteredTetrahedron := by
  constructor
  · rintro ⟨t, ht, htlo, hthi, hx, hy⟩
    have hzt : t = (1 - z 2) / 2 := by
      simp only [phi_apply_two, ell_eq] at ht
      apply (mul_left_cancel₀ h_ne_zero)
      nlinarith [ht]
    subst t
    simp only [phi_apply_zero, phi_apply_one, abs_mul, abs_neg,
      abs_of_pos ell_pos] at hx hy
    have hx' : |z 0| ≤ h * (2 - z 2) := by
      apply (mul_le_mul_iff_right₀ ell_pos).mp
      nlinarith [ell_mul_h]
    have hy' : |z 1| ≤ h * z 2 := by
      apply (mul_le_mul_iff_right₀ ell_pos).mp
      nlinarith [ell_mul_h]
    exact ⟨by linarith, by linarith, hy', hx'⟩
  · rintro ⟨hzlo, hzhi, hy, hx⟩
    refine ⟨(1 - z 2) / 2, ?_, by linarith, by linarith, ?_, ?_⟩
    · simp only [phi_apply_two, ell_eq]; ring
    · simp only [phi_apply_zero, abs_mul, abs_neg, abs_of_pos ell_pos]
      have hm := (mul_le_mul_iff_right₀ ell_pos).mpr hx
      nlinarith [ell_mul_h]
    · simp only [phi_apply_one, abs_mul, abs_of_pos ell_pos]
      have hm := (mul_le_mul_iff_right₀ ell_pos).mpr hy
      nlinarith [ell_mul_h]

lemma phi_surjective : Function.Surjective phi := by
  intro z
  refine ⟨!₂[-z 0 / ell, z 1 / ell, 1 - z 2 / ell], ?_⟩
  ext i
  fin_cases i <;> simp [phi] <;> field_simp [ell_ne_zero]

theorem phi_image_tetrahedron :
    phi '' uncenteredTetrahedron = centeredTetrahedron := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (phi_membership x).mpr hx
  · intro hz
    obtain ⟨x, rfl⟩ := phi_surjective z
    exact ⟨x, (phi_membership x).mp hz, rfl⟩

lemma shifted_reflection_isometry :
    Isometry (fun z : Space => reflection z + !₂[0, 0, 1]) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_add_right, reflection_isometry.dist_eq]

theorem phi_euclideanHausdorffMeasure (S : Set Space) :
    Measure.euclideanHausdorffMeasure 2 (phi '' S) =
      ‖ell‖₊ ^ 2 • Measure.euclideanHausdorffMeasure 2 S := by
  have himage : phi '' S =
      ell • ((fun z : Space => reflection z + !₂[0, 0, 1]) '' S) := by
    change phi '' S = (fun x : Space => ell • x) '' ((fun z : Space => reflection z + !₂[0, 0, 1]) '' S)
    rw [Set.image_image]
    congr 1
    funext z
    exact phi_decomposition z
  rw [himage, Measure.euclideanHausdorffMeasure_smul₀ 2 ell_ne_zero]
  rw [shifted_reflection_isometry.euclideanHausdorffMeasure_image]

theorem phi_area (S : Set Space) :
    (Measure.euclideanHausdorffMeasure 2 (phi '' S)).toReal =
      (1 / 8 : ℝ) * (Measure.euclideanHausdorffMeasure 2 S).toReal := by
  rw [phi_euclideanHausdorffMeasure, ENNReal.toReal_smul]
  simp only [NNReal.smul_def, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos ell_pos, ell_sq, smul_eq_mul]

end RationalSimilarity

end

end OAI
