import OAI.MeasureTheory.Falconer.Angular.GnomonicCap

namespace OAI

/-! # The small chart law lies in the unit cube used by radial pruning -/

namespace Falconer
open Metric MeasureTheory
variable {n : ℕ}

lemma gnomonic_cap_coordinates_norm_le (w : Sphere (n+1)) {ρ : ℝ}
    (hw : dist w (gnomonicChart (0 : Space n)) ≤ ρ) (hρ : ρ ≤ 1/2) :
    ‖gnomonicCoordinates w‖ ≤ 2*ρ := by
  have hw0 := gnomonic_cap_first_coordinate w (hw.trans hρ)
  have hp : 0 < (w:Space (n+1)) 0 := by linarith
  let v : Space (n+1) := (w:Space (n+1))-northLift 0
  let t : Space n := WithLp.toLp 2 (fun i => v i.succ)
  have ht : ‖t‖ ≤ ‖v‖ := by
    have hs : ‖t‖^2 ≤ ‖v‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
      simp only [t]
      exact le_add_of_nonneg_left (sq_nonneg (v 0))
    nlinarith [norm_nonneg t,norm_nonneg v]
  have hv : ‖v‖ ≤ ρ := by
    simpa only [v,Subtype.dist_eq,gnomonicChart_zero_coe,dist_eq_norm] using hw
  have he : gnomonicCoordinates w = ((w:Space (n+1)) 0)⁻¹ • t := by
    ext i
    simp only [gnomonicCoordinates_apply,PiLp.smul_apply,smul_eq_mul,t,
      v,PiLp.sub_apply,northLift_succ,PiLp.zero_apply,sub_zero,div_eq_mul_inv]
    ring
  have hi : ((w:Space (n+1)) 0)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ hp).mpr
    linarith
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
  exact (mul_le_mul_of_nonneg_left (ht.trans hv) (inv_nonneg.mpr hp.le)).trans
    (mul_le_mul_of_nonneg_right hi (by linarith [norm_nonneg v]))

lemma small_gnomonic_cap_law (ν : Measure (Sphere (n+1)))
    (hν : ∀ᵐ w ∂ν, dist w (gnomonicChart (0 : Space n)) ≤ 1/8) :
    ∀ᵐ p ∂Measure.map gnomonicCoordinates ν, ‖p‖ ≤ 1/4 := by
  rw [ae_map_iff gnomonicCoordinates_measurable.aemeasurable
    (measurableSet_le measurable_norm measurable_const)]
  filter_upwards [hν] with w hw
  have hh := gnomonic_cap_coordinates_norm_le w hw (by norm_num : (1/8:ℝ) ≤ 1/2)
  norm_num at hh ⊢
  exact hh

end Falconer

end OAI
