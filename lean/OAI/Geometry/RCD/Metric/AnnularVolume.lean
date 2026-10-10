import OAI.Geometry.RCD.Metric.VolumeRegime

namespace OAI

/-! # A definite annulus in the almost-Euclidean volume regime -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

/-- The relative quarter-error gives positive volume and a definite
exterior annulus in every dimension at least two. -/
theorem relative_volume_annulus {n : ℕ} (hn : 2 ≤ n) {r omega V W : ℝ}
    (hr : 0 < r) (homega : 0 < omega)
    (hV : |V / (omega * r ^ n) - 1| ≤ 1 / 4)
    (hW : |W / (omega * (2 * r) ^ n) - 1| ≤ 1 / 4) :
    0 < V ∧ 2 * V ≤ W := by
  have hden : 0 < omega * r ^ n := mul_pos homega (pow_pos hr _)
  have hden2 : 0 < omega * (2 * r) ^ n := mul_pos homega (pow_pos (by positivity) _)
  have hvlo : (3 / 4 : ℝ) * (omega * r ^ n) ≤ V := by
    have hh := (abs_le.mp hV).1
    have hdiv : (3 / 4 : ℝ) ≤ V / (omega * r ^ n) := by linarith
    exact (le_div_iff₀ hden).mp hdiv
  have hvhi : V ≤ (5 / 4 : ℝ) * (omega * r ^ n) := by
    have hh := (abs_le.mp hV).2
    have hdiv : V / (omega * r ^ n) ≤ (5 / 4 : ℝ) := by linarith
    exact (div_le_iff₀ hden).mp hdiv
  have hwlo : (3 / 4 : ℝ) * (omega * (2 * r) ^ n) ≤ W := by
    have hh := (abs_le.mp hW).1
    have hdiv : (3 / 4 : ℝ) ≤ W / (omega * (2 * r) ^ n) := by linarith
    exact (le_div_iff₀ hden2).mp hdiv
  have hp : (4 : ℝ) ≤ 2 ^ n := by
    calc
      (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hn
  have hscale : 4 * (omega * r ^ n) ≤ omega * (2 * r) ^ n := by
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_right hp hden.le]
  exact ⟨by nlinarith, by nlinarith⟩

/-- An explicit radius cap for every curvature test on a 64-fold ball. -/
theorem curvature_bound_sixtyfour {K r : ℝ} (hr : 0 ≤ r)
    (hcap : r ≤ 1 / (64 * (|K| + 1))) : -1 ≤ K * (64 * r) ^ 2 := by
  have hb : r * (64 * (|K| + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 64 * (|K| + 1))).mp hcap
  have hx : 0 ≤ 64 * r := by positivity
  have hx1 : 64 * r ≤ 1 := by nlinarith [abs_nonneg K]
  have hsq : (64 * r) ^ 2 ≤ 64 * r := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq (abs_nonneg K)
  have hk := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg (64 * r))
  nlinarith

end RegularPointCoordinates

end

end OAI
