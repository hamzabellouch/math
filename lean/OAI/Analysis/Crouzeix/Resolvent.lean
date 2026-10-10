import Mathlib
import OAI.Analysis.Crouzeix.NumericalRange

namespace OAI

/-! Resolvent. -/

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem nonneg_re_inner_of_unit (T : Operator H)
    (h : ∀ x : H, ‖x‖ = 1 → 0 ≤ (⟪x, T x⟫_ℂ).re) (x : H) :
    0 ≤ (⟪x, T x⟫_ℂ).re := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let v : H := (‖x‖ : ℂ)⁻¹ • x
  have hv : ‖v‖ = 1 := by simp [v, norm_smul, hn.ne']
  have ht := h v hv
  have he : (⟪v, T v⟫_ℂ).re = ‖x‖⁻¹ * (‖x‖⁻¹ * (⟪x, T x⟫_ℂ).re) := by
    simp [v, Complex.mul_re, mul_comm]
  rw [he] at ht
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hn)).mp
    ((mul_nonneg_iff_of_pos_left (inv_pos.mpr hn)).mp ht)

variable [CompleteSpace H]

theorem isPositive_add_adjoint_of_unit (T : Operator H)
    (h : ∀ x : H, ‖x‖ = 1 → 0 ≤ (⟪x, T x⟫_ℂ).re) :
    (T + star T).IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨IsSelfAdjoint.add_star_self T, fun x => ?_⟩
  have ht := nonneg_re_inner_of_unit T h x
  change 0 ≤ (⟪(T + star T) x, x⟫_ℂ).re
  simp only [add_apply, inner_add_left,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
    Complex.add_re]
  have he : (⟪T x, x⟫_ℂ).re = (⟪x, T x⟫_ℂ).re := inner_re_symm (𝕜 := ℂ) _ _
  rw [he]
  linarith only [ht]

theorem isPositive_supporting_halfplane (A : Operator H) (z q : ℂ)
    (hsupport : ∀ w ∈ numericalRange A, 0 ≤ (star q * (z - w)).re) :
    (star q • (algebraMap ℂ (Operator H) z - A) +
      star (star q • (algebraMap ℂ (Operator H) z - A))).IsPositive := by
  apply isPositive_add_adjoint_of_unit
  intro x hx
  have h := hsupport ⟪x, A x⟫_ℂ ⟨x, hx, rfl⟩
  simpa [inner_smul_right, inner_sub_right, inner_self_eq_norm_sq_to_K, hx,
    Algebra.algebraMap_eq_smul_one] using h

theorem resolvent_hermitian_congruence (A : Operator H) (z q : ℂ)
    (hz : IsUnit (algebraMap ℂ (Operator H) z - A)) :
    let E := algebraMap ℂ (Operator H) z - A
    let R := Ring.inverse E
    star R * (star q • E + star (star q • E)) * R = q • R + star (q • R) := by
  dsimp only
  let E := algebraMap ℂ (Operator H) z - A
  let R := Ring.inverse E
  have hER : E * R = 1 := Ring.mul_inverse_cancel E hz
  change star R * (star q • E + star (star q • E)) * R = q • R + star (q • R)
  have hstar : star R * star E = 1 := by rw [← star_mul, hER, star_one]
  calc
    star R * (star q • E + star (star q • E)) * R =
        star q • (star R * (E * R)) + q • ((star R * star E) * R) := by
      simp only [star_smul, star_star, mul_add, add_mul, mul_smul_comm,
        smul_mul_assoc, mul_assoc]
    _ = star q • star R + q • R := by rw [hER, hstar, mul_one, one_mul]
    _ = q • R + star (q • R) := by rw [star_smul, add_comm]

theorem isPositive_original_resolvent (A : Operator H) (z q : ℂ)
    (hz : IsUnit (algebraMap ℂ (Operator H) z - A))
    (hsupport : ∀ w ∈ numericalRange A, 0 ≤ (star q * (z - w)).re) :
    (q • Ring.inverse (algebraMap ℂ (Operator H) z - A) +
      star (q • Ring.inverse (algebraMap ℂ (Operator H) z - A))).IsPositive := by
  have hp := (isPositive_supporting_halfplane A z q hsupport).adjoint_conj
    (Ring.inverse (algebraMap ℂ (Operator H) z - A))
  change (star (Ring.inverse (algebraMap ℂ (Operator H) z - A)) *
    (star q • (algebraMap ℂ (Operator H) z - A) +
      star (star q • (algebraMap ℂ (Operator H) z - A))) *
      Ring.inverse (algebraMap ℂ (Operator H) z - A)).IsPositive at hp
  rwa [resolvent_hermitian_congruence A z q hz] at hp

theorem isPositive_original_resolvent_of_not_mem (A : Operator H) (z q : ℂ)
    (hz : z ∉ numericalClosure A)
    (hsupport : ∀ w ∈ numericalRange A, 0 ≤ (star q * (z - w)).re) :
    (q • Ring.inverse (algebraMap ℂ (Operator H) z - A) +
      star (q • Ring.inverse (algebraMap ℂ (Operator H) z - A))).IsPositive := by
  apply isPositive_original_resolvent A z q _ hsupport
  change z ∈ resolventSet ℂ A
  by_contra he
  exact hz (spectrum_subset_numericalClosure A he)

theorem isPositive_contraction_defect (T : Operator H) (hn : ‖T‖ ≤ 1) :
    (1 - star T * T).IsPositive := by
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨by simp [IsSelfAdjoint, star_mul], fun x => ?_⟩
  have ht : ‖T x‖ ≤ ‖x‖ := by
    calc
      ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = ‖x‖ := one_mul _
  change 0 ≤ RCLike.re ⟪x - ContinuousLinearMap.adjoint T (T x), x⟫_ℂ
  simp only [inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    map_sub, ← norm_sq_eq_re_inner]
  nlinarith only [ht, norm_nonneg x, norm_nonneg (T x)]

theorem disk_resolvent_congruence (T : Operator H) (hT : IsUnit (1 - T)) :
    let R := Ring.inverse (1 - T)
    star R * (1 - star T * T) * R = R + star R - 1 := by
  let E := 1 - T
  let R := Ring.inverse E
  have hER : E * R = 1 := Ring.mul_inverse_cancel E hT
  have hstar : star R * star E = 1 := by rw [← star_mul, hER, star_one]
  have hid : 1 - star T * T = star E + E - star E * E := by
    simp only [E, star_sub, star_one]
    noncomm_ring
  change star R * (1 - star T * T) * R = R + star R - 1
  rw [hid]
  calc
    star R * (star E + E - star E * E) * R =
        (star R * star E) * R + star R * (E * R) -
          (star R * star E) * (E * R) := by noncomm_ring
    _ = R + star R - 1 := by rw [hstar, hER, one_mul, mul_one, one_mul]

def diskDensity (D : Operator H) (ζ : ℂ) : Operator H :=
  Ring.inverse (1 - ζ⁻¹ • D) + star (Ring.inverse (1 - ζ⁻¹ • D)) - 1

theorem isPositive_diskResolvent (T : Operator H) (hn : ‖T‖ ≤ 1)
    (hu : IsUnit (1 - T)) :
    (Ring.inverse (1 - T) + star (Ring.inverse (1 - T)) - 1).IsPositive := by
  have hp := (isPositive_contraction_defect T hn).adjoint_conj (Ring.inverse (1 - T))
  have hp' : (star (Ring.inverse (1 - T)) * (1 - star T * T) *
      Ring.inverse (1 - T)).IsPositive := by
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.comp_assoc] using hp
  rw [disk_resolvent_congruence T hu] at hp'
  exact hp'

theorem isPositive_diskDensity (D : Operator H) (hD : ‖D‖ ≤ 1) (ζ : ℂ)
    (hζ : ‖ζ‖ = 1) (hu : IsUnit (1 - ζ⁻¹ • D)) : (diskDensity D ζ).IsPositive := by
  apply isPositive_diskResolvent _ _ hu
  rw [norm_smul, norm_inv, hζ, inv_one, one_mul]
  exact hD

omit [CompleteSpace H] in
theorem disk_resolvent_isUnit (D : Operator H)
    (hD : ∀ z ∈ spectrum ℂ D, ‖z‖ < 1) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    IsUnit (1 - ζ⁻¹ • D) := by
  have hn : ζ ≠ 0 := by intro he; simp [he] at hζ
  have hr : IsUnit (algebraMap ℂ (Operator H) ζ - D) := by
    change ζ ∈ resolventSet ℂ D
    by_contra he
    have := hD ζ he
    rw [hζ] at this
    exact lt_irrefl _ this
  have he : 1 - ζ⁻¹ • D = ζ⁻¹ • (algebraMap ℂ (Operator H) ζ - D) := by
    simp [Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul, hn]
  rw [he, Algebra.smul_def]
  exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero hn)).map (algebraMap ℂ (Operator H))).mul hr

theorem isPositive_diskDensity_of_spectrum (D : Operator H)
    (hn : ‖D‖ ≤ 1) (hD : ∀ z ∈ spectrum ℂ D, ‖z‖ < 1)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) : (diskDensity D ζ).IsPositive :=
  isPositive_diskDensity D hn ζ hζ (disk_resolvent_isUnit D hD ζ hζ)

end CrouzeixHilbert

end

end OAI
