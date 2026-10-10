import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFresnelPhase

namespace OAI

/-! # Evaluating the limiting quadratic Gaussian coefficient -/

namespace Ostmann

private theorem sqrt_quarter_reciprocal {b : ℝ} :
    Real.sqrt ((1 / (2 * b)) / 2) = 1 / (2 * Real.sqrt b) := by
  rw [div_div, show 2 * b * 2 = 4 * b by ring, Real.sqrt_div,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  all_goals norm_num

 theorem quadratic_fresnel_coefficient_positive {a t : ℝ} (hat : 0 < a * t) :
    quadraticFresnelCoefficient 0 a t =
      ((1 / (2 * Real.sqrt (a * t)) : ℝ) : ℂ) * (1 - Complex.I) := by
  let b := a * t
  have hb : 0 < b := hat
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have he : (1 : ℂ) / (2 * Complex.I * (b : ℂ)) =
      -((1 / (2 * b) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  unfold quadraticFresnelCoefficient
  rw [Complex.ofReal_zero, zero_add]
  change ((1 : ℂ) / (2 * Complex.I * (b : ℂ))) ^ (1 / 2 : ℂ) = _
  rw [he, quadratic_half_negative_imaginary (by positivity), sqrt_quarter_reciprocal]

 theorem quadratic_fresnel_coefficient_negative {a t : ℝ} (hat : a * t < 0) :
    quadraticFresnelCoefficient 0 a t =
      ((1 / (2 * Real.sqrt (-(a * t))) : ℝ) : ℂ) * (1 + Complex.I) := by
  let b := -(a * t)
  have hb : 0 < b := neg_pos.mpr hat
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have he : (1 : ℂ) / (2 * Complex.I * (a * t : ℝ)) =
      ((1 / (2 * b) : ℝ) : ℂ) * Complex.I := by
    have hbt : a * t = -b := by dsimp [b]; ring
    rw [hbt]
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq]
  unfold quadraticFresnelCoefficient
  rw [Complex.ofReal_zero, zero_add, he,
    quadratic_half_positive_imaginary (by positivity), sqrt_quarter_reciprocal]

end Ostmann

end OAI
