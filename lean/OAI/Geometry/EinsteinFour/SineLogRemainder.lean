import OAI.Geometry.EinsteinFour.SineLogPolynomial
import Mathlib.Analysis.Real.Pi.Bounds

namespace OAI

/-! A logarithmic sine bound supplying the strict volume correction. -/
namespace PositiveEinsteinFour.Jacobi
open Filter Set
open scoped Topology
noncomputable section

private def weightedSinc (x : ℝ) : ℝ := Real.exp (sineLogPolynomial x) * Real.sinc x

private theorem weightedSinc_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt weightedSinc
      (-(Real.exp (sineLogPolynomial x) *
        (sineCotPolynomial x * Real.sin x - x * Real.cos x)) / x ^ 2) x := by
  have h := ((sineLogPolynomial_hasDerivAt x).exp).mul
    ((Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx)
  have he : weightedSinc =ᶠ[𝓝 x] (fun y => Real.exp (sineLogPolynomial y) * (Real.sin y / y)) := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hx] with y hy
    exact congrArg (fun r => Real.exp (sineLogPolynomial y) * r) (Real.sinc_of_ne_zero hy)
  convert h.congr_of_eventuallyEq he using 1
  dsimp [sineLogRate, sineCotPolynomial]
  field_simp
  ring

theorem sineLogPolynomial_le_neg_log {x : ℝ} (hx : 0 < x) (hxπ : x < Real.pi) :
    sineLogPolynomial x ≤ -Real.log (Real.sin x / x) := by
  have hcontinuous : Continuous weightedSinc :=
    (Real.continuous_exp.comp (continuous_iff_continuousAt.mpr
      (fun s => (sineLogPolynomial_hasDerivAt s).continuousAt))).mul Real.continuous_sinc
  have hm : AntitoneOn weightedSinc (Icc 0 x) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hcontinuous.continuousOn
    · intro s hs
      rw [interior_Icc] at hs
      exact (weightedSinc_hasDerivAt hs.1.ne').hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hW := sineLogWronskian_nonneg hs.1.le (hs.2.trans hxπ).le
      have hB : 0 ≤ sineCotPolynomial s * Real.sin s - s * Real.cos s := by
        exact (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp hW
      exact div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (mul_nonneg (Real.exp_pos _).le hB)) (sq_nonneg s)
  have hq := hm (by simp [hx.le]) (by simp [hx.le]) hx.le
  have hs : 0 < Real.sin x / x := div_pos (Real.sin_pos_of_pos_of_lt_pi hx hxπ) hx
  have hle : Real.sin x / x ≤ Real.exp (-sineLogPolynomial x) := by
    have h' : Real.exp (sineLogPolynomial x) * (Real.sin x / x) ≤ 1 := by
      simpa [weightedSinc, sineLogPolynomial, Real.sinc_of_ne_zero hx.ne'] using hq
    calc
      _ ≤ 1 / Real.exp (sineLogPolynomial x) :=
        (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using h')
      _ = _ := by rw [Real.exp_neg, one_div]
  have hl := (Real.log_le_iff_le_exp hs).mpr hle
  linarith

theorem sine_log_remainder_lower {x : ℝ} (hx : 0 < x) (hxπ : x < Real.pi) :
    (x / Real.pi) ^ 4 / 2 + (x / Real.pi) ^ 6 / 3 ≤
      -Real.log (Real.sin x / x) - x ^ 2 / 6 := by
  have hp : (157 / 50 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hp4 : 90 ≤ Real.pi ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 157 / 50) hp 4
    norm_num at h
    linarith
  have hp6 : 945 ≤ Real.pi ^ 6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 157 / 50) hp 6
    norm_num at h
    linarith
  have h4 : (x / Real.pi) ^ 4 / 2 ≤ x ^ 4 / 180 := by
    rw [div_pow, div_div]
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have h6 : (x / Real.pi) ^ 6 / 3 ≤ x ^ 6 / 2835 := by
    rw [div_pow, div_div]
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have h := sineLogPolynomial_le_neg_log hx hxπ
  unfold sineLogPolynomial at h
  linarith

end
end PositiveEinsteinFour.Jacobi

end OAI
