import OAI.NumberTheory.Ostmann.QuadraticCenter.ScaleBounds

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter

def quadraticAtom (a : ℂ) (κ h θ R : ℝ) : ℂ :=
  (((Real.sqrt R)⁻¹ : ℝ) : ℂ) * a * weylPhase ((h + θ) * κ) * cutoffFourier (κ / R)

theorem inv_sqrt_scale_nonneg_le_one {R : ℝ} (hR : 1 ≤ R) :
    0 ≤ (Real.sqrt R)⁻¹ ∧ (Real.sqrt R)⁻¹ ≤ 1 := by
  have hs : 1 ≤ Real.sqrt R := by simpa using Real.sqrt_le_sqrt hR
  exact ⟨inv_nonneg.mpr (Real.sqrt_nonneg _), inv_le_one_of_one_le₀ hs⟩

theorem norm_quadraticAtom {R : ℝ} (hR : 1 ≤ R) (a : ℂ) (κ h θ : ℝ) :
    ‖quadraticAtom a κ h θ R‖ ≤ ‖a‖ * cutoffFourierBound := by
  have hi := inv_sqrt_scale_nonneg_le_one hR
  simp only [quadraticAtom, norm_mul, weylPhase_norm, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hi.1]
  calc
    _ ≤ 1 * ‖a‖ * cutoffFourierBound := by
      gcongr
      exacts [hi.2, norm_cutoff_fourier_le _]
    _ = _ := by ring

theorem phase_quadratic_parameter_bound (κ h θ θ' : ℝ) :
    ‖weylPhase ((h + θ) * κ) - weylPhase ((h + θ') * κ)‖ ≤
      (2 * Real.pi) * |κ| * |θ - θ'| := by
  have he : (h + θ) * κ - (h + θ') * κ = κ * (θ - θ') := by ring
  have hp := weylPhase_lipschitz ((h + θ) * κ) ((h + θ') * κ)
  rw [he, abs_mul] at hp
  simpa only [mul_assoc] using hp

theorem quadraticAtom_theta_lipschitz {R : ℝ} (hR : 1 ≤ R)
    (a : ℂ) (κ h θ θ' : ℝ) :
    ‖quadraticAtom a κ h θ R - quadraticAtom a κ h θ' R‖ ≤
      ‖a‖ * cutoffFourierBound * (2 * Real.pi) * |κ| * |θ - θ'| := by
  have hi := inv_sqrt_scale_nonneg_le_one hR
  have he : quadraticAtom a κ h θ R - quadraticAtom a κ h θ' R =
      (((Real.sqrt R)⁻¹ : ℝ) : ℂ) * a *
        (weylPhase ((h + θ) * κ) - weylPhase ((h + θ') * κ)) * cutoffFourier (κ / R) := by
    unfold quadraticAtom
    ring
  rw [he]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hi.1]
  calc
    _ ≤ 1 * ‖a‖ * ((2 * Real.pi) * |κ| * |θ - θ'|) * cutoffFourierBound := by
      gcongr
      exacts [hi.2, phase_quadratic_parameter_bound κ h θ θ', norm_cutoff_fourier_le _]
    _ = _ := by ring

theorem quadraticAtom_scale_lipschitz {R R' : ℝ} (hR : 1 ≤ R) (hR' : 1 ≤ R')
    (a : ℂ) (κ h θ : ℝ) :
    ‖quadraticAtom a κ h θ R - quadraticAtom a κ h θ R'‖ ≤
      ‖a‖ * cutoffFourierBound * (1 + |κ|) * |R - R'| := by
  have hi := inv_sqrt_scale_nonneg_le_one hR'
  have he : quadraticAtom a κ h θ R - quadraticAtom a κ h θ R' =
      a * weylPhase ((h + θ) * κ) *
        ((((Real.sqrt R)⁻¹ - (Real.sqrt R')⁻¹ : ℝ) : ℂ) * cutoffFourier (κ / R) +
          (((Real.sqrt R')⁻¹ : ℝ) : ℂ) * (cutoffFourier (κ / R) - cutoffFourier (κ / R'))) := by
    unfold quadraticAtom
    push_cast
    ring
  rw [he, norm_mul, norm_mul, weylPhase_norm, mul_one]
  calc
    _ ≤ ‖a‖ *
        (‖((((Real.sqrt R)⁻¹ - (Real.sqrt R')⁻¹ : ℝ) : ℂ) * cutoffFourier (κ / R))‖ +
          ‖(((Real.sqrt R')⁻¹ : ℝ) : ℂ) * (cutoffFourier (κ / R) - cutoffFourier (κ / R'))‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = ‖a‖ * (|(Real.sqrt R)⁻¹ - (Real.sqrt R')⁻¹| * ‖cutoffFourier (κ / R)‖ +
        (Real.sqrt R')⁻¹ * ‖cutoffFourier (κ / R) - cutoffFourier (κ / R')‖) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hi.1]
    _ ≤ ‖a‖ * (|R - R'| * cutoffFourierBound +
        1 * (cutoffFourierBound * |κ| * |R - R'|)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply add_le_add
      · exact mul_le_mul (inv_sqrt_scale_lipschitz hR hR') (norm_cutoff_fourier_le _)
          (norm_nonneg _) (abs_nonneg _)
      · exact mul_le_mul hi.2 (cutoff_div_scale_lipschitz hR hR' κ)
          (norm_nonneg _) zero_le_one
    _ = _ := by ring

theorem quadraticAtom_parameters_lipschitz {R R' : ℝ} (hR : 1 ≤ R) (hR' : 1 ≤ R')
    (a : ℂ) (κ h θ θ' : ℝ) :
    ‖quadraticAtom a κ h θ R - quadraticAtom a κ h θ' R'‖ ≤
      ‖a‖ * cutoffFourierBound *
        ((2 * Real.pi) * |κ| * |θ - θ'| + (1 + |κ|) * |R - R'|) := by
  have ht := quadraticAtom_theta_lipschitz hR a κ h θ θ'
  have hr := quadraticAtom_scale_lipschitz hR hR' a κ h θ'
  have hn := norm_sub_le_norm_sub_add_norm_sub (quadraticAtom a κ h θ R) (quadraticAtom a κ h θ' R)
    (quadraticAtom a κ h θ' R')
  nlinarith

end Ostmann.QuadraticCenter

end

end OAI
