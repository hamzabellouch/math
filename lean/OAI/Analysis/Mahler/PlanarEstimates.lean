import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-! An elementary uniform reciprocal-arctangent estimate for the
planar construction, with the explicit absolute constant C=2. -/

namespace SymmetricMahler
open Real

lemma arctan_le_argument {x : ℝ} (hx : 0 ≤ x) : arctan x ≤ x := by
  simpa only [tan_arctan] using
    Real.le_tan (arctan_nonneg.mpr hx) (arctan_lt_pi_div_two x)

lemma half_argument_le_arctan {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ arctan x := by
  have hs : 0 < Real.sqrt (1 + x^2) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt (1 + x^2) ≤ 2 := by
    apply Real.sqrt_le_iff.2
    constructor
    · norm_num
    · nlinarith [sq_nonneg x]
  calc
    x / 2 ≤ x / Real.sqrt (1 + x^2) :=
      div_le_div_of_nonneg_left hx hs hs2
    _ = sin (arctan x) := (sin_arctan x).symm
    _ ≤ arctan x := Real.sin_le (arctan_nonneg.mpr hx)

/-- A uniform reciprocal bound with the explicit absolute constant 2. -/
theorem reciprocal_arctan_bound {v : ℝ} (hv : 0 < v) :
    1 / arctan v ≤ 2 / Real.pi + 2 / v := by
  have ha : 0 < arctan v := arctan_pos.mpr hv
  rcases le_total v 1 with hv1 | h1v
  · have hlower := half_argument_le_arctan hv.le hv1
    have hrecip : 1 / arctan v ≤ 2 / v :=
      (div_le_div_iff₀ ha hv).2 (by nlinarith)
    have hnonneg : 0 ≤ 2 / Real.pi := by positivity
    linarith
  · have hquarter : Real.pi / 4 ≤ arctan v := by
      simpa only [arctan_one] using arctan_strictMono.monotone h1v
    have hcompl : Real.pi / 2 - arctan v ≤ 1 / v := by
      rw [← arctan_inv_of_pos hv, one_div]
      exact arctan_le_argument (inv_nonneg.mpr hv.le)
    have hcompl' : (Real.pi / 2 - arctan v) * v ≤ 1 :=
      (le_div_iff₀ hv).1 hcompl
    have hap : 1 ≤ arctan v * Real.pi := by
      nlinarith [Real.pi_gt_three]
    have hrearrange : 2 / Real.pi + 2 / v =
        (2 * v + 2 * Real.pi) / (Real.pi * v) := by
      field_simp
    rw [hrearrange]
    apply (div_le_div_iff₀ ha (mul_pos Real.pi_pos hv)).2
    nlinarith

end SymmetricMahler

namespace SymmetricMahler
open Real

/-- The angular-speed expression B as a real scalar function. -/
noncomputable def angularSpeed (r θ : ℝ) : ℝ :=
  (4 / Real.pi^2) * arctan (2 * r * sin θ / (1 - r^2))

/-- The reciprocal angular-speed estimate, with C = π²/4. -/
theorem angular_speed_inverse_bound {r θ : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hθ : 0 < sin θ) :
    1 / angularSpeed r θ ≤ Real.pi / 2 +
      (Real.pi^2 / 4) * ((1-r^2) / (r * sin θ)) := by
  have hden : 0 < 1-r^2 := by nlinarith
  have hv : 0 < 2*r*sin θ/(1-r^2) := by positivity
  have ha : arctan (2*r*sin θ/(1-r^2)) ≠ 0 := ne_of_gt (arctan_pos.mpr hv)
  have hp := mul_le_mul_of_nonneg_left (reciprocal_arctan_bound hv)
    (show 0 ≤ Real.pi^2/4 by positivity)
  calc
    1 / angularSpeed r θ = (Real.pi^2/4) *
        (1/arctan (2*r*sin θ/(1-r^2))) := by
      dsimp [angularSpeed]
      field_simp
    _ ≤ (Real.pi^2/4) * (2/Real.pi + 2/(2*r*sin θ/(1-r^2))) := hp
    _ = Real.pi / 2 + (Real.pi^2/4)*((1-r^2)/(r*sin θ)) := by
      field_simp
      ; ring

/-- The pointwise estimate on the first half of the tail integral. -/
theorem tail_first_half {L t : ℝ} (hL : 0 < L) (_ht : 0 ≤ t)
    (htL : t ≤ L/2) :
    exp (-t) * sqrt (t/(L-t)) ≤ exp (-t) := by
  have hden : 0 < L-t := by linarith
  have hr : t/(L-t) ≤ 1 := (div_le_one hden).2 (by linarith)
  have hs : sqrt (t/(L-t)) ≤ 1 := by
    apply sqrt_le_iff.2
    exact ⟨by norm_num, by simpa using hr⟩
  nlinarith [exp_pos (-t)]

/-- The pointwise integrable singular majorant on the second half. -/
theorem tail_second_half {L t : ℝ} (_hL : 0 < L)
    (ht : L/2 ≤ t) (htL : t < L) :
    exp (-t) * sqrt (t/(L-t)) ≤
      exp (-L/2) * sqrt L / sqrt (L-t) := by
  have ht0 : 0 ≤ t := by linarith
  have hden : 0 < sqrt (L-t) := sqrt_pos.2 (by linarith)
  have hexp : exp (-t) ≤ exp (-L/2) := exp_le_exp.mpr (by linarith)
  have hs : sqrt t / sqrt (L-t) ≤ sqrt L / sqrt (L-t) :=
    div_le_div_of_nonneg_right (sqrt_le_sqrt htL.le) hden.le
  rw [sqrt_div ht0]
  calc
    exp (-t) * (sqrt t / sqrt (L-t)) ≤ exp (-L/2) *
        (sqrt L / sqrt (L-t)) :=
      mul_le_mul hexp hs (by positivity) (by positivity)
    _ = exp (-L/2) * sqrt L / sqrt (L-t) := by ring

/-- The elementary maximization for the uniform-L bound. -/
theorem uniform_tail_constant (L : ℝ) :
    1 + 2*L*exp (-L/2) ≤ 1 + 4/exp 1 := by
  have h := mul_exp_neg_le_exp_neg_one (L/2)
  simp only [exp_neg, div_eq_mul_inv] at h
  have he : exp (-L/2) = (exp (L/2))⁻¹ := by rw [← exp_neg]; congr 1 ; ring
  rw [he]
  simp only [div_eq_mul_inv]
  nlinarith

end SymmetricMahler

end OAI
