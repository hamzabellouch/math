import OAI.MeasureTheory.Falconer.Angular.GnomonicLaw

namespace OAI

/-! # A small spherical cap has bounded original affine coordinates -/

namespace Falconer
open Metric MeasureTheory
variable {n : ℕ}

@[simp] theorem northLift_zero_vector : northLift (0 : Space n) =
    WithLp.toLp 2 (Fin.cons 1 (fun _ => 0)) := rfl

@[simp] theorem northLift_zero_norm : ‖northLift (0 : Space n)‖ = 1 := by
  have hh := northLift_norm_sq (0 : Space n)
  simp only [norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),add_zero] at hh
  nlinarith [norm_nonneg (northLift (0 : Space n))]

@[simp] theorem gnomonicChart_zero_coe :
    (gnomonicChart (0 : Space n) : Space (n+1)) = northLift 0 := by
  change ‖northLift (0 : Space n)‖⁻¹ • northLift 0 = _
  rw [northLift_zero_norm,inv_one,one_smul]

theorem inner_northLift_zero (w : Space (n+1)) :
    inner ℝ w (northLift (0 : Space n)) = w 0 := by
  rw [PiLp.inner_apply,Fin.sum_univ_succ]
  simp

theorem gnomonic_cap_first_coordinate (w : Sphere (n+1))
    (hw : dist w (gnomonicChart (0 : Space n)) ≤ 1/2) :
    7/8 ≤ (w:Space (n+1)) 0 := by
  have hh := norm_sub_sq_real (w:Space (n+1)) (northLift (0 : Space n))
  rw [sphere_norm,northLift_zero_norm,inner_northLift_zero] at hh
  have hd : ‖(w:Space (n+1))-northLift (0 : Space n)‖ ≤ 1/2 := by
    simpa only [Subtype.dist_eq,gnomonicChart_zero_coe,dist_eq_norm] using hw
  nlinarith [norm_nonneg ((w:Space (n+1))-northLift (0 : Space n))]

theorem gnomonic_cap_coordinates_norm (w : Sphere (n+1))
    (hw : dist w (gnomonicChart (0 : Space n)) ≤ 1/2) :
    ‖gnomonicCoordinates w‖ ≤ 1 := by
  have hw0 := gnomonic_cap_first_coordinate w hw
  have hp : 0 < (w:Space (n+1)) 0 := by linarith
  have hn : ‖northLift (gnomonicCoordinates w)‖ = ((w:Space (n+1)) 0)⁻¹ := by
    rw [northLift_gnomonicCoordinates w hp,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hp),sphere_norm,mul_one]
  have hbound : ‖northLift (gnomonicCoordinates w)‖ ≤ 8/7 := by
    rw [hn,← one_div]
    apply (div_le_iff₀ hp).mpr
    linarith
  have hs := northLift_norm_sq (gnomonicCoordinates w)
  nlinarith [norm_nonneg (northLift (gnomonicCoordinates w)),
    norm_nonneg (gnomonicCoordinates w)]

theorem gnomonic_cap_law_bounded (ν : Measure (Sphere (n+1)))
    (hν : ∀ᵐ (w : Sphere (n+1)) ∂ν,
      dist w (gnomonicChart (0 : Space n)) ≤ 1/2) :
    ∀ᵐ p ∂Measure.map gnomonicCoordinates ν, ‖p‖ ≤ 1 := by
  rw [ae_map_iff gnomonicCoordinates_measurable.aemeasurable
    (measurableSet_le measurable_norm measurable_const)]
  filter_upwards [hν] with w hw
  exact gnomonic_cap_coordinates_norm w hw

end Falconer

end OAI
