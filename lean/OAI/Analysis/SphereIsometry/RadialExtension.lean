import OAI.Analysis.SphereIsometry.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Affine.MazurUlam

namespace OAI

/-!
# The radial extension of a sphere isometry with zero defect

The extension is defined on actual vectors, including zero. A zero cross-radius
bound gives its all-pairs isometry; sphere surjectivity gives its surjectivity.
Mazur–Ulam then supplies real linearity. Uniqueness is proved against arbitrary
real-linear extensions, without assuming they are continuous or surjective.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The actual radial extension, with a separate zero branch. -/
def radialExtension (f : UnitSphere X ≃ᵢ UnitSphere Y) (x : X) : Y := by
  classical
  exact if hx : x = 0 then 0 else ‖x‖ • (f (normalize x hx) : Y)

@[simp] theorem radialExtension_zero (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    radialExtension f 0 = 0 := by
  simp [radialExtension]

theorem radialExtension_of_ne_zero (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (x : X) (hx : x ≠ 0) :
    radialExtension f x = ‖x‖ • (f (normalize x hx) : Y) := by
  simp only [radialExtension, dite_eq_right hx]

@[simp] theorem radialExtension_norm (f : UnitSphere X ≃ᵢ UnitSphere Y) (x : X) :
    ‖radialExtension f x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    simp only [radialExtension_zero, norm_zero]
  · rw [radialExtension_of_ne_zero f x hx,
      norm_smul_of_nonneg (norm_nonneg x), UnitSphere.norm_coe, mul_one]

/-- Every nonnegative radial representation has the expected image. -/
theorem radialExtension_smul_unit (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (r : ℝ) (hr : 0 ≤ r) (u : UnitSphere X) :
    radialExtension f (r • (u : X)) = r • (f u : Y) := by
  by_cases hr0 : r = 0
  · subst r
    simp only [zero_smul, radialExtension_zero]
  · have hn : ‖r • (u : X)‖ = r := by
      rw [norm_smul_of_nonneg hr, UnitSphere.norm_coe, mul_one]
    have hne : r • (u : X) ≠ 0 := by
      intro h
      apply hr0
      rw [← hn, h, norm_zero]
    have hnormalize : normalize (r • (u : X)) hne = u := by
      apply Subtype.ext
      change ‖r • (u : X)‖⁻¹ • (r • (u : X)) = (u : X)
      rw [hn, smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [radialExtension_of_ne_zero f _ hne, hn, hnormalize]

@[simp] theorem radialExtension_unit (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (u : UnitSphere X) : radialExtension f (u : X) = (f u : Y) := by
  simpa only [one_smul] using radialExtension_smul_unit f 1 zero_le_one u

/-- The zero bound gives exact preservation at every radius in the closed unit interval. -/
theorem crossRadius_eq_of_zero_defect (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (u v : UnitSphere X) :
    ‖(f u : Y) - q • (f v : Y)‖ = ‖(u : X) - q • (v : X)‖ := by
  exact sub_eq_zero.mp (signedDefect_eq_zero_of_bound_zero h0 hq u v)

/-- Factor by the larger positive radius; the smaller radius may be zero. -/
theorem scaled_norm_sub_eq (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (u v : UnitSphere X) (a b : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a) :
    ‖a • (f u : Y) - b • (f v : Y)‖ = ‖a • (u : X) - b • (v : X)‖ := by
  have hq : b / a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hb ha.le, (div_le_one ha).mpr hba⟩
  have hab : a * (b / a) = b := by
    rw [div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ (ne_of_gt ha), mul_one]
  calc
    ‖a • (f u : Y) - b • (f v : Y)‖ =
        ‖a • ((f u : Y) - (b / a) • (f v : Y))‖ := by
      rw [smul_sub, smul_smul, hab]
    _ = a * ‖(f u : Y) - (b / a) • (f v : Y)‖ :=
      norm_smul_of_nonneg ha.le _
    _ = a * ‖(u : X) - (b / a) • (v : X)‖ := by
      rw [crossRadius_eq_of_zero_defect f h0 (b / a) hq u v]
    _ = ‖a • ((u : X) - (b / a) • (v : X))‖ :=
      (norm_smul_of_nonneg ha.le _).symm
    _ = ‖a • (u : X) - b • (v : X)‖ := by
      rw [smul_sub, smul_smul, hab]

/-- Every pair is covered, including zero vectors and either order of radii. -/
theorem radialExtension_norm_sub (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (x y : X) :
    ‖radialExtension f x - radialExtension f y‖ = ‖x - y‖ := by
  by_cases hx : x = 0
  · subst x
    simpa only [radialExtension_zero, zero_sub, norm_neg] using radialExtension_norm f y
  by_cases hy : y = 0
  · subst y
    simpa only [radialExtension_zero, sub_zero] using radialExtension_norm f x
  have hordered (a b : X) (ha : a ≠ 0) (hb : b ≠ 0) (hba : ‖b‖ ≤ ‖a‖) :
      ‖radialExtension f a - radialExtension f b‖ = ‖a - b‖ := by
    have h := scaled_norm_sub_eq f h0 (normalize a ha) (normalize b hb)
      ‖a‖ ‖b‖ (norm_pos_iff.mpr ha) (norm_nonneg b) hba
    rw [norm_smul_normalize, norm_smul_normalize] at h
    simpa only [radialExtension_of_ne_zero f a ha,
      radialExtension_of_ne_zero f b hb] using h
  rcases le_total ‖y‖ ‖x‖ with hle | hle
  · exact hordered x y hx hy hle
  · calc
      ‖radialExtension f x - radialExtension f y‖ =
          ‖radialExtension f y - radialExtension f x‖ := norm_sub_rev _ _
      _ = ‖y - x‖ := hordered y x hy hx hle
      _ = ‖x - y‖ := norm_sub_rev _ _

theorem radialExtension_isometry (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) : Isometry (radialExtension f) := by
  apply Isometry.of_dist_eq
  intro x y
  simpa only [dist_eq_norm] using radialExtension_norm_sub f h0 x y

/-- Surjectivity follows directly from the actual inverse on unit spheres. -/
theorem radialExtension_surjective (f : UnitSphere X ≃ᵢ UnitSphere Y) :
    Function.Surjective (radialExtension f) := by
  intro y
  by_cases hy : y = 0
  · subst y
    exact ⟨0, radialExtension_zero f⟩
  · refine ⟨‖y‖ • (f.symm (normalize y hy) : X), ?_⟩
    rw [radialExtension_smul_unit f ‖y‖ (norm_nonneg y), f.apply_symm_apply]
    exact norm_smul_normalize y hy

/-- The metric equivalence is built only after isometry and surjectivity are proved. -/
def radialIsometryEquiv (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) : X ≃ᵢ Y where
  toEquiv := Equiv.ofBijective (radialExtension f)
    ⟨(radialExtension_isometry f h0).injective, radialExtension_surjective f⟩
  isometry_toFun := radialExtension_isometry f h0

@[simp] theorem coe_radialIsometryEquiv (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) : ⇑(radialIsometryEquiv f h0) = radialExtension f := rfl

@[simp] theorem radialIsometryEquiv_apply (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (x : X) :
    radialIsometryEquiv f h0 x = radialExtension f x := rfl

/-- Mazur–Ulam applied to the derived whole-space isometry fixing zero. -/
def radialLinearIsometryEquiv (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) : X ≃ₗᵢ[ℝ] Y :=
  (radialIsometryEquiv f h0).toRealLinearIsometryEquivOfMapZero
    (by change radialExtension f 0 = 0; exact radialExtension_zero f)

@[simp] theorem coe_radialLinearIsometryEquiv (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) :
    ⇑(radialLinearIsometryEquiv f h0) = radialExtension f := rfl

@[simp] theorem radialLinearIsometryEquiv_apply (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (x : X) :
    radialLinearIsometryEquiv f h0 x = radialExtension f x := rfl

@[simp] theorem radialLinearIsometryEquiv_unit (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (h0 : HasDefectBound f 0) (u : UnitSphere X) :
    radialLinearIsometryEquiv f h0 (u : X) = (f u : Y) :=
  radialExtension_unit f u

/-- Any real-linear extension has the radial formula, without additional hypotheses on it. -/
theorem linear_extension_eq_radial (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (L : X →ₗ[ℝ] Y) (hL : ∀ u : UnitSphere X, L (u : X) = (f u : Y)) (x : X) :
    L x = radialExtension f x := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, radialExtension_zero]
  · calc
      L x = L (‖x‖ • (normalize x hx : X)) :=
        congrArg L (norm_smul_normalize x hx).symm
      _ = ‖x‖ • L (normalize x hx : X) := L.map_smul _ _
      _ = ‖x‖ • (f (normalize x hx) : Y) := by rw [hL]
      _ = radialExtension f x := (radialExtension_of_ne_zero f x hx).symm

theorem linear_extension_unique (f : UnitSphere X ≃ᵢ UnitSphere Y)
    (L K : X →ₗ[ℝ] Y)
    (hL : ∀ u : UnitSphere X, L (u : X) = (f u : Y))
    (hK : ∀ u : UnitSphere X, K (u : X) = (f u : Y)) : L = K := by
  apply LinearMap.ext
  intro x
  exact (linear_extension_eq_radial f L hL x).trans
    (linear_extension_eq_radial f K hK x).symm

/-- The conditional extension endpoint; the main theorem supplies the proved zero bound. -/
theorem existsUnique_linearIsometryEquiv_of_zero_defect
    (f : UnitSphere X ≃ᵢ UnitSphere Y) (h0 : HasDefectBound f 0) :
    ∃! L : X ≃ₗᵢ[ℝ] Y, ∀ u : UnitSphere X, L (u : X) = (f u : Y) := by
  refine ⟨radialLinearIsometryEquiv f h0, ?_, ?_⟩
  · exact radialLinearIsometryEquiv_unit f h0
  · intro L hL
    apply LinearIsometryEquiv.ext
    intro x
    change L x = radialExtension f x
    exact linear_extension_eq_radial f L.toLinearEquiv.toLinearMap hL x

end Tingley

end

end OAI
