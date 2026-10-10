import Mathlib

namespace OAI

/-!
The radial normal of a spherical surface immersion.  The identities are for
actual Fréchet derivatives and the orthogonal projection defining the second
fundamental form, not an abstract second-jet model.
-/

noncomputable section

open scoped ContDiff

namespace ClosedSurfaceR4.SphericalJets

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 4)

theorem radial_first {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ x, ‖F x‖ = 1) (x v : Plane) :
    inner ℝ (F x) (fderiv ℝ F x v) = 0 := by
  have he : (fun y => inner ℝ (F y) (F y)) = fun _ => (1 : ℝ) := by
    funext y
    rw [real_inner_self_eq_norm_sq, hunit y]
    norm_num
  have hd := hF.differentiable (by simp) x
  have hh := congrArg (fun A : Plane →L[ℝ] ℝ => A v)
    (congrArg (fun f : Plane → ℝ => fderiv ℝ f x) he)
  rw [fderiv_inner_apply ℝ hd hd] at hh
  simp only [fderiv_const_apply, zero_apply, real_inner_comm (F x)] at hh
  linarith

lemma derivative_apply {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    (x v w : Plane) :
    fderiv ℝ (fun y => fderiv ℝ F y w) x v =
      fderiv ℝ (fderiv ℝ F) x v w := by
  have hDF := (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  rw [fderiv_clm_apply hDF (differentiableAt_const w)]
  simp

theorem radial_second {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ x, ‖F x‖ = 1) (x v w : Plane) :
    inner ℝ (F x) (fderiv ℝ (fderiv ℝ F) x v w) =
      -inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w) := by
  have he : (fun y => inner ℝ (F y) (fderiv ℝ F y w)) = fun _ => (0 : ℝ) := by
    funext y
    exact radial_first hF hunit y w
  have hh := congrArg (fun A : Plane →L[ℝ] ℝ => A v)
    (congrArg (fun f : Plane → ℝ => fderiv ℝ f x) he)
  have hd := hF.differentiable (by simp) x
  have hDF := (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  rw [fderiv_inner_apply ℝ hd (hDF.clm_apply (differentiableAt_const w)),
    derivative_apply hF] at hh
  simp only [fderiv_const_apply, zero_apply] at hh
  linarith

theorem raw_second_inward_pairing {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ x, ‖F x‖ = 1) (x v w : Plane) :
    inner ℝ (fderiv ℝ (fderiv ℝ F) x v w) (-F x) =
      inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w) := by
  rw [inner_neg_right, real_inner_comm, radial_second hF hunit, neg_neg]

/-- The actual normal plane of the immersed tangent plane. -/
def normalSpace (F : Plane → Space) (x : Plane) : Submodule ℝ Space :=
  (LinearMap.range (fderiv ℝ F x).toLinearMap)ᗮ

/-- The Euclidean second fundamental form obtained by normal projection. -/
def secondForm (F : Plane → Space) (x v w : Plane) : Space :=
  (normalSpace F x).starProjection (fderiv ℝ (fderiv ℝ F) x v w)

theorem inward_normal_mem {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ x, ‖F x‖ = 1) (x : Plane) : -F x ∈ normalSpace F x := by
  rw [normalSpace, Submodule.mem_orthogonal]
  rintro _ ⟨v, rfl⟩
  change inner ℝ (fderiv ℝ F x v) (-F x) = 0
  rw [inner_neg_right, real_inner_comm, radial_first hF hunit, neg_zero]

theorem secondForm_inward_pairing {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ x, ‖F x‖ = 1) (x v w : Plane) :
    inner ℝ (secondForm F x v w) (-F x) =
      inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w) := by
  rw [secondForm, Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (inward_normal_mem hF hunit x)]
  exact raw_second_inward_pairing hF hunit x v w

theorem secondForm_inward_pos {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ x, ‖F x‖ = 1) (x v : Plane)
    (hImm : Function.Injective (fderiv ℝ F x)) (hv : v ≠ 0) :
    0 < inner ℝ (secondForm F x v v) (-F x) := by
  rw [secondForm_inward_pairing hF hunit]
  apply real_inner_self_pos.mpr
  intro h
  apply hv
  exact hImm (by simpa only [map_zero] using h)

theorem secondForm_ne_zero {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ x, ‖F x‖ = 1) (x v : Plane)
    (hImm : Function.Injective (fderiv ℝ F x)) (hv : v ≠ 0) :
    secondForm F x v v ≠ 0 := by
  have hp := secondForm_inward_pos hF hunit x v hImm hv
  intro h
  rw [h, inner_zero_left] at hp
  exact lt_irrefl 0 hp

/-- Removing the radial component gives the second fundamental form within
the unit sphere. -/
def sphericalSecondForm (F : Plane → Space) (x v w : Plane) : Space :=
  secondForm F x v w +
    (inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w)) • F x

theorem sphericalSecondForm_radial_orthogonal {F : Plane → Space}
    (hF : ContDiff ℝ ∞ F) (hunit : ∀ x, ‖F x‖ = 1) (x v w : Plane) :
    inner ℝ (sphericalSecondForm F x v w) (F x) = 0 := by
  have hp := secondForm_inward_pairing hF hunit x v w
  rw [inner_neg_right] at hp
  have hnorm : inner ℝ (F x) (F x) = 1 := by
    rw [real_inner_self_eq_norm_sq, hunit x]
    norm_num
  simp only [sphericalSecondForm, inner_add_left, real_inner_smul_left, hnorm, mul_one]
  linarith

theorem radial_secondForm_decomposition (F : Plane → Space) (x v w : Plane) :
    secondForm F x v w = sphericalSecondForm F x v w +
      (inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w)) • (-F x) := by
  simp only [sphericalSecondForm, smul_neg, add_neg_cancel_right]

lemma firstDerivative_scale {F : Plane → Space} (hF : ContDiff ℝ ∞ F) (r : ℝ) (x : Plane) :
    fderiv ℝ (fun y => r • F y) x = r • fderiv ℝ F x :=
  fderiv_const_smul (hF.differentiable (by simp) x) r

lemma secondDerivative_scale {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    (r : ℝ) (x v w : Plane) :
    fderiv ℝ (fderiv ℝ (fun y => r • F y)) x v w =
      r • fderiv ℝ (fderiv ℝ F) x v w := by
  have he : fderiv ℝ (fun y => r • F y) = fun y => r • fderiv ℝ F y := by
    funext y
    exact firstDerivative_scale hF r y
  rw [he]
  change fderiv ℝ (r • fderiv ℝ F) x v w = _
  rw [fderiv_const_smul
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x) r]
  rfl

lemma normalSpace_scale {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    {r : ℝ} (hr : r ≠ 0) (x : Plane) :
    normalSpace (fun y => r • F y) x = normalSpace F x := by
  unfold normalSpace
  rw [firstDerivative_scale hF r x]
  change (LinearMap.range (r • (fderiv ℝ F x).toLinearMap))ᗮ = _
  rw [LinearMap.range_smul _ _ hr]

theorem secondForm_scale {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    {r : ℝ} (hr : r ≠ 0) (x v w : Plane) :
    secondForm (fun y => r • F y) x v w = r • secondForm F x v w := by
  unfold secondForm
  simp only [normalSpace_scale hF hr, secondDerivative_scale hF, map_smul]

/-- Equation `spherical-radial-form` for the actual second fundamental form.
The scaled induced metric appears in the coefficient of the inward radial
normal, as in the manuscript. -/
theorem scaled_spherical_radial_form {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    {r : ℝ} (hr : r ≠ 0) (x v w : Plane) :
    secondForm (fun y => r • F y) x v w = r • sphericalSecondForm F x v w +
      (r⁻¹ * inner ℝ (fderiv ℝ (fun y => r • F y) x v)
        (fderiv ℝ (fun y => r • F y) x w)) • (-F x) := by
  rw [secondForm_scale hF hr, radial_secondForm_decomposition F,
    firstDerivative_scale hF r x]
  simp only [smul_apply, real_inner_smul_left,
    real_inner_smul_right, smul_add, smul_smul]
  congr 1
  congr 1
  field_simp

end ClosedSurfaceR4.SphericalJets

end

end OAI
