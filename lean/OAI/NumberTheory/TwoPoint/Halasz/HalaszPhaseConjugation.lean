import OAI.NumberTheory.TwoPoint.Halasz.HalaszTriangleIntegral

namespace OAI

/-! Reflection of the logarithmic phase, needed for both signs of a
frequency difference in the sparse Gram kernel. -/
namespace TwoPointCorrelations

open MeasureTheory Complex
open scoped ComplexConjugate

lemma halasz_log_phase_neg (u v x : ℝ) :
    halaszLogPhase (-u) (-v) x = conj (halaszLogPhase u v x) := by
  unfold halaszLogPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_sub, conj_ofReal, conj_I, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_neg]
  ring

lemma halasz_log_affine_integral_neg (u v m c a b : ℝ) :
    (∫ x in a..b, ((m*x+c:ℝ):ℂ)*halaszLogPhase (-u) (-v) x) =
      conj (∫ x in a..b, ((m*x+c:ℝ):ℂ)*halaszLogPhase u v x) := by
  simp_rw [halasz_log_phase_neg]
  have he (x : ℝ) : ((m*x+c:ℝ):ℂ)*conj (halaszLogPhase u v x) =
      conj (((m*x+c:ℝ):ℂ)*halaszLogPhase u v x) := by simp
  simp_rw [he]
  unfold intervalIntegral
  rw [integral_conj, integral_conj, map_sub]

lemma halasz_triangle_integral_neg (N u v : ℝ) :
    halaszTriangleIntegral N (-u) (-v) = conj (halaszTriangleIntegral N u v) := by
  unfold halaszTriangleIntegral
  simp only [sub_eq_add_neg]
  rw [halasz_log_affine_integral_neg, halasz_log_affine_integral_neg, map_add]

lemma halasz_triangle_stationary_abs (N u v : ℝ) (hN : 0 < N) (hu : u ≠ 0) :
    ‖halaszTriangleIntegral N u v‖ ≤ 110*N/Real.sqrt |u| := by
  rcases lt_or_gt_of_ne hu with hn | hp
  · have hh := halasz_triangle_stationary N (-u) (-v) hN (neg_pos.mpr hn)
    rw [halasz_triangle_integral_neg, norm_conj, ← abs_of_neg hn] at hh
    exact hh
  · simpa only [abs_of_pos hp] using halasz_triangle_stationary N u v hN hp

end TwoPointCorrelations

end OAI
