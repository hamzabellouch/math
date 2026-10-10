import Mathlib.Tactic

namespace OAI

/-! # Uniform error when the Gaussian exponent approaches the sharp value -/

namespace RegularPointCoordinates

theorem gaussian_action_slack {T η R d : ℝ} (hT : 0 < T) (hη : 0 < η)
    (hR : 0 ≤ R) (hd : 0 ≤ d) (hdR : d ≤ 2*R) :
    let a := η*T/(2*(R^2+1));
    d^2/(2*T)-2*d^2/((4+a)*T) ≤ η/4 := by
  dsimp only
  let a := η*T/(2*(R^2+1))
  have ha : 0 < a := by dsimp only [a]; positivity
  change d^2/(2*T)-2*d^2/((4+a)*T) ≤ _
  have hden : 0 < 8*T := by positivity
  have hpow : d^2 ≤ 4*R^2 := by nlinarith
  calc
    _ = a*d^2/(2*(4+a)*T) := by field_simp; ring
    _ ≤ a*d^2/(8*T) := div_le_div_of_nonneg_left (by positivity) hden (by nlinarith)
    _ ≤ a*(4*R^2)/(8*T) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow ha.le) hden.le
    _ = η*R^2/(4*(R^2+1)) := by dsimp only [a]; field_simp; ring
    _ ≤ η/4 := by
      apply (div_le_iff₀ (by positivity : 0 < 4*(R^2+1))).mpr
      nlinarith

end RegularPointCoordinates

end OAI
