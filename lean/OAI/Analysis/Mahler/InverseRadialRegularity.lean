import OAI.Analysis.Mahler.ConformalRadialRegularity

namespace OAI

noncomputable section
open Complex Set Metric
namespace MahlerConformal

def inverseRadiusRadialSlope (u : ℂ) : ℝ :=
  2 * (u.re * (inverseF u * deriv F (inverseF u)).re +
    u.im * (inverseF u * deriv F (inverseF u)).im) / ‖deriv F (inverseF u)‖^2

/-- The derivative in the outward radial direction, at a point of Omega. -/
theorem hasDerivAt_inverseRadius_radial {u : ℂ} (hu : u ∈ Omega) :
    HasDerivAt (fun t : ℝ => Complex.normSq (inverseF ((t : ℂ)*u)))
      (inverseRadiusRadialSlope u) 1 := by
  have hl : HasDerivAt (fun t : ℂ => t*u) u (1 : ℂ) := by
    simpa using (hasDerivAt_id (1 : ℂ)).mul_const u
  have hi : HasDerivAt inverseF (deriv F (inverseF u))⁻¹ ((fun t : ℂ => t*u) 1) := by
    simpa using hasDerivAt_inverseF hu
  have hf := (hi.comp (1 : ℂ) hl).comp_ofReal
  have hn := hasDerivAt_normSq hf
  simp only [Function.comp_apply, Complex.ofReal_one, one_mul] at hn
  convert hn using 1 ; try rfl
  unfold inverseRadiusRadialSlope
  rw [← div_eq_inv_mul]
  simp only [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
    Complex.normSq_eq_norm_sq]
  ring

theorem inverseRadiusRadialSlope_pos {u : ℂ} (hu : u ∈ Omega) (hu0 : u ≠ 0) :
    0 < inverseRadiusRadialSlope u := by
  have hw := inverseF_mem hu
  have hw0 : inverseF u ≠ 0 := (inverseF_eq_zero_iff hu).not.mpr hu0
  have hp := F_radial_pairing_pos (by simpa using hw) hw0
  rw [inverseF_right hu] at hp
  exact div_pos (mul_pos (by norm_num) hp)
    (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (deriv_F_ne_zero (by simpa using hw))))

@[simp] lemma inverseRadiusRadialSlope_zero : inverseRadiusRadialSlope 0 = 0 := by
  simp [inverseRadiusRadialSlope]

theorem inverseRadiusRadialSlope_nonneg {u : ℂ} (hu : u ∈ Omega) :
    0 ≤ inverseRadiusRadialSlope u := by
  by_cases h : u = 0
  · simp [h]
  · exact (inverseRadiusRadialSlope_pos hu h).le

end MahlerConformal

end

end OAI
