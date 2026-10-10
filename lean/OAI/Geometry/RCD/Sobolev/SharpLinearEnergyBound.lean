import OAI.Geometry.RCD.Metric.EuclideanBallMeanDerivative

namespace OAI

/-! # Removing the volume enlargement from infinitesimal transport tests -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem sharp_linear_energy_bound {n : ℕ} (D : Euclidean n →L[ℝ] ℝ)
    {C : ℝ} (hC : 0≤C)
    (hb : ∀ v : Euclidean n, ∀ θ : ℝ, 0<θ → θ<1 →
      ∀ c : ℝ, 1+‖v‖<c → (D v)^2≤‖v‖^2*(c/θ)^n*C) :
    ‖D‖^2≤C := by
  have hv (v : Euclidean n) : (D v)^2≤‖v‖^2*C := by
    have hcont : Continuous (fun t : ℝ =>
        ‖v‖^2*((1+t*(‖v‖+1))*(1+t))^n*C) := by fun_prop
    have hlim : Tendsto (fun t : ℝ =>
        ‖v‖^2*((1+t*(‖v‖+1))*(1+t))^n*C) (𝓝[>] 0) (𝓝 (‖v‖^2*C)) := by
      simpa only [zero_mul,add_zero,mul_one,one_pow] using
        (hcont.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0<t := ht
    have hθ : 0<(1+t)⁻¹ := by positivity
    have hθ1 : (1+t)⁻¹<1 := (inv_lt_one₀ (by positivity)).mpr (by linarith)
    have hc : 1+‖t • v‖<1+t*(‖v‖+1) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht0]
      nlinarith
    have hh := hb (t • v) (1+t)⁻¹ hθ hθ1 (1+t*(‖v‖+1)) hc
    rw [map_smul,smul_eq_mul,norm_smul,Real.norm_eq_abs,abs_of_pos ht0,
      div_inv_eq_mul,mul_pow,mul_pow] at hh
    have he : t^2*(D v)^2≤t^2*(‖v‖^2*((1+t*(‖v‖+1))*(1+t))^n*C) := by
      nlinarith only [hh]
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos ht0)).mp he
  have hn : ‖D‖≤Real.sqrt C := by
    apply D.opNorm_le_bound (Real.sqrt_nonneg C)
    intro v
    have hh := hv v
    have hs := Real.sq_sqrt hC
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (D v),sq_abs (D v),norm_nonneg v,
      mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg v)]
  nlinarith [norm_nonneg D,Real.sqrt_nonneg C,Real.sq_sqrt hC]

end RegularPointCoordinates

end

end OAI
