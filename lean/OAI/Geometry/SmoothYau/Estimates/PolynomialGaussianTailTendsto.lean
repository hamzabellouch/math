import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ContDiffSmoothFiniteWave

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace YauCounterexamples

lemma polynomial_gaussian_tail_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => t^12*Real.exp (-a*t^2)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 6 a ha).comp
    (tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by norm_num) : Tendsto (fun t : ℝ => t^2) atTop atTop)
  simpa [Function.comp_def,Real.rpow_natCast,←pow_mul] using h

lemma quartic_inverse_bounds {t : ℝ} (ht : 1 ≤ t) :
    0 < t ∧ 1 ≤ t^4 ∧ (t^4)⁻¹ ≤ t⁻¹ ∧ (Real.sqrt (t^4))⁻¹ ≤ 2/t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hs : Real.sqrt (t^4) = t^2 := by
    rw [show t^4 = (t^2)^2 by ring,Real.sqrt_sq (sq_nonneg t)]
  have h4 : 1 ≤ t^4 := one_le_pow₀ ht
  have h14 : (t^4)⁻¹ ≤ t⁻¹ := inv_anti₀ ht0 (le_self_pow₀ ht (by norm_num : (4 : ℕ) ≠ 0))
  have h12 : (t^2)⁻¹ ≤ t⁻¹ := inv_anti₀ ht0 (le_self_pow₀ ht (by norm_num : (2 : ℕ) ≠ 0))
  refine ⟨ht0,h4,h14,?_⟩
  rw [hs]
  exact h12.trans (by rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr ht0])

lemma quartic_near_endpoint {t : ℝ} (ht : 1 ≤ t) (x y q : NormalWaveSpace)
    (hx : ‖x-q‖ ≤ t⁻¹) (hsep : t^4*‖y-x‖ ≤ 1) :
    ‖x-q‖ ≤ 2/t ∧ ‖y-q‖ ≤ 2/t := by
  obtain ⟨ht0,ht4,hinv,_⟩ := quartic_inverse_bounds ht
  have hyx : ‖y-x‖ ≤ (t^4)⁻¹ := by
    have hh : ‖y-x‖ ≤ 1/(t^4) := (le_div_iff₀ (show 0 < t^4 by positivity)).mpr (by nlinarith [hsep])
    simpa only [one_div] using hh
  have htinv : t⁻¹ ≤ 2/t := by rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr ht0]
  refine ⟨hx.trans htinv,?_⟩
  calc
    _ ≤ ‖y-x‖+‖x-q‖ := by simpa only [sub_add_sub_cancel] using norm_add_le (y-x) (x-q)
    _ ≤ t⁻¹+t⁻¹ := add_le_add (hyx.trans hinv) hx
    _ = 2/t := by ring

lemma quartic_far_endpoint {t : ℝ} (ht : 2 ≤ t) (x y q : NormalWaveSpace)
    (hx : t⁻¹ < ‖x-q‖) (hsep : t^4*‖y-x‖ ≤ 1) :
    t^2/4 ≤ t^4*‖y-q‖^2 := by
  have ht0 : 0 < t := by linarith
  have ht4 : 0 < t^4 := by positivity
  have hyx : ‖y-x‖ ≤ (t^4)⁻¹ := by
    have hh : ‖y-x‖ ≤ 1/(t^4) := (le_div_iff₀ ht4).mpr (by nlinarith [hsep])
    simpa only [one_div] using hh
  have hpow : 2*t ≤ t^4 := by
    have hs : 4 ≤ t^2 := by nlinarith
    nlinarith [sq_nonneg (t^2-2),sq_nonneg (t-1)]
  have hinv : (t^4)⁻¹ ≤ (2*t)⁻¹ := inv_anti₀ (by positivity) hpow
  have htriangle : ‖x-q‖ ≤ ‖y-x‖+‖y-q‖ := by
    have h := norm_add_le (x-y) (y-q)
    rw [sub_add_sub_cancel,norm_sub_rev x y] at h
    exact h
  have hdist : (2*t)⁻¹ ≤ ‖y-q‖ := by
    have he : t⁻¹ = 2*(2*t)⁻¹ := by field_simp
    linarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (2*t)⁻¹) hdist 2
  have hh := mul_le_mul_of_nonneg_left hs ht4.le
  have he : t^4*(2*t)⁻¹^2 = t^2/4 := by field_simp; ring
  rwa [he] at hh
end YauCounterexamples
end

end OAI
