import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.ReciprocalPhase

def phase (θ : ℝ) : ℂ := Complex.exp ((2 * θ : ℝ) * Complex.I) - 1

def inversePhase (θ : ℝ) : ℂ := (phase θ)⁻¹

lemma phase_re (θ : ℝ) : (phase θ).re = -2 * Real.sin θ ^ 2 := by
  simp only [phase, Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.one_re,
    Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq θ]

lemma phase_im (θ : ℝ) : (phase θ).im = 2 * Real.sin θ * Real.cos θ := by
  simp only [phase, Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.one_im, sub_zero, Real.sin_two_mul]

lemma phase_normSq (θ : ℝ) : Complex.normSq (phase θ) = 4 * Real.sin θ ^ 2 := by
  rw [Complex.normSq_apply, phase_re, phase_im]
  calc
    _ = 4 * Real.sin θ ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
    _ = 4 * Real.sin θ ^ 2 := by rw [Real.sin_sq_add_cos_sq]; ring

lemma inversePhase_re {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    (inversePhase θ).re = -1 / 2 := by
  rw [inversePhase, Complex.inv_re, phase_re, phase_normSq]
  field_simp
  ring

lemma inversePhase_im {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    (inversePhase θ).im = -Real.cot θ / 2 := by
  rw [inversePhase, Complex.inv_im, phase_im, phase_normSq, Real.cot_eq_cos_div_sin]
  field_simp
  ring

lemma phase_norm {θ : ℝ} (hs : 0 ≤ Real.sin θ) : ‖phase θ‖ = 2 * Real.sin θ := by
  have hn := norm_nonneg (phase θ)
  have he : ‖phase θ‖ ^ 2 = 4 * Real.sin θ ^ 2 := by
    rw [Complex.sq_norm, phase_normSq]
  nlinarith

lemma inversePhase_norm {θ : ℝ} (hs : 0 ≤ Real.sin θ) :
    ‖inversePhase θ‖ = 1 / (2 * Real.sin θ) := by
  rw [inversePhase, norm_inv, phase_norm hs, one_div]

lemma strictAntiOn_cot : StrictAntiOn Real.cot (Set.Ioo 0 Real.pi) := by
  intro x hx y hy hxy
  have hsx := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hsy := Real.sin_pos_of_pos_of_lt_pi hy.1 hy.2
  have hsd := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hxy)
    (show y - x < Real.pi by linarith [hx.1, hy.2])
  rw [Real.sin_sub] at hsd
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  apply (div_lt_div_iff₀ hsy hsx).mpr
  nlinarith

lemma inversePhase_im_strictMonoOn :
    StrictMonoOn (fun θ => (inversePhase θ).im) (Set.Ioo 0 Real.pi) := by
  intro x hx y hy hxy
  change (inversePhase x).im < (inversePhase y).im
  rw [inversePhase_im (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2)),
    inversePhase_im (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hy.1 hy.2))]
  have h := strictAntiOn_cot hx hy hxy
  linarith

lemma sin_pi_mul_lower {β x : ℝ} (hβ : 0 ≤ β) (hx : β ≤ x) (hx' : x ≤ 1 - β) :
    2 * β ≤ Real.sin (Real.pi * x) := by
  have hx0 : 0 ≤ x := hβ.trans hx
  have hx1 : x ≤ 1 := by linarith
  by_cases hhalf : x ≤ 1 / 2
  · have hs := Real.mul_le_sin (mul_nonneg Real.pi_pos.le hx0)
      (show Real.pi * x ≤ Real.pi / 2 by nlinarith [Real.pi_pos])
    have he : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
    rw [he] at hs
    linarith
  · have hs := Real.mul_le_sin (mul_nonneg Real.pi_pos.le (show 0 ≤ 1 - x by linarith))
      (show Real.pi * (1 - x) ≤ Real.pi / 2 by nlinarith [Real.pi_pos])
    have he : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by field_simp
    have he2 : Real.pi * (1 - x) = Real.pi - Real.pi * x := by ring
    rw [he, he2, Real.sin_pi_sub] at hs
    linarith

lemma inversePhase_norm_le {β x : ℝ} (hβ : 0 < β) (hx : β ≤ x) (hx' : x ≤ 1 - β) :
    ‖inversePhase (Real.pi * x)‖ ≤ 1 / (4 * β) := by
  have hs := sin_pi_mul_lower hβ.le hx hx'
  have hs0 : 0 ≤ Real.sin (Real.pi * x) := by linarith
  rw [inversePhase_norm hs0]
  apply one_div_le_one_div_of_le (by positivity)
  linarith

lemma inversePhase_scaled_re {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    (inversePhase (Real.pi * x)).re = -1 / 2 := by
  apply inversePhase_re
  apply ne_of_gt
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith [Real.pi_pos]

lemma inversePhase_scaled_im_strictMonoOn :
    StrictMonoOn (fun x => (inversePhase (Real.pi * x)).im) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  apply inversePhase_im_strictMonoOn
  · constructor
    · exact mul_pos Real.pi_pos hx.1
    · nlinarith [Real.pi_pos, hx.2]
  · constructor
    · exact mul_pos Real.pi_pos hy.1
    · nlinarith [Real.pi_pos, hy.2]
  · exact mul_lt_mul_of_pos_left hxy Real.pi_pos

lemma phase_ne_zero {θ : ℝ} (hs : Real.sin θ ≠ 0) : phase θ ≠ 0 := by
  intro h
  have hr := phase_re θ
  rw [h, Complex.zero_re] at hr
  have hsq := sq_pos_of_ne_zero hs
  nlinarith

/-- The unit-modulus exponential used in the first-derivative sum. -/
def unitPhase (θ : ℝ) : ℂ := Complex.exp ((2 * θ : ℝ) * Complex.I)

lemma unitPhase_add (φ θ : ℝ) : unitPhase (φ + θ) = unitPhase φ * unitPhase θ := by
  unfold unitPhase
  rw [show ((2 * (φ + θ) : ℝ) : ℂ) * Complex.I =
      ((2 * φ : ℝ) : ℂ) * Complex.I + ((2 * θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_add _ _

lemma norm_unitPhase (θ : ℝ) : ‖unitPhase θ‖ = 1 := by
  simp [unitPhase, Complex.norm_exp]

lemma inversePhase_mul_increment {θ : ℝ} (hs : Real.sin θ ≠ 0) (φ : ℝ) :
    inversePhase θ * (unitPhase (φ + θ) - unitPhase φ) = unitPhase φ := by
  rw [unitPhase_add]
  have hp : unitPhase θ - 1 = phase θ := rfl
  calc
    inversePhase θ * (unitPhase φ * unitPhase θ - unitPhase φ) =
        unitPhase φ * (inversePhase θ * (unitPhase θ - 1)) := by ring
    _ = unitPhase φ := by
      rw [hp, inversePhase, inv_mul_cancel₀ (phase_ne_zero hs), mul_one]

lemma inversePhase_norm_sub {x y : ℝ} (hx : x ∈ Set.Ioo 0 Real.pi)
    (hy : y ∈ Set.Ioo 0 Real.pi) (hxy : x ≤ y) :
    ‖inversePhase y - inversePhase x‖ = (inversePhase y).im - (inversePhase x).im := by
  have hsx := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2)
  have hsy := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hy.1 hy.2)
  have hre : (inversePhase y - inversePhase x).re = 0 := by
    rw [Complex.sub_re, inversePhase_re hsx, inversePhase_re hsy]
    ring
  have him : 0 ≤ (inversePhase y).im - (inversePhase x).im := by
    exact sub_nonneg.mpr (inversePhase_im_strictMonoOn.monotoneOn hx hy hxy)
  have hn := norm_nonneg (inversePhase y - inversePhase x)
  have he := Complex.sq_norm (inversePhase y - inversePhase x)
  rw [Complex.normSq_apply, hre, Complex.sub_im] at he
  nlinarith

end Problem337.ReciprocalPhase

end

end OAI
