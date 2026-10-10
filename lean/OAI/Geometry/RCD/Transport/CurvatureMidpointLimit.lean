import OAI.Geometry.RCD.Transport.CurvatureCompressionBound

namespace OAI

/-! # The exact CD midpoint coefficient at vanishing rescaled curvature -/

open Filter
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem curvature_scaled_sqrt_tendsto_zero {K : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hK : K ≤ 0) {r ε : ℕ → ℝ}
    (hr : ∀ k, 0 ≤ r k) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -ε k ≤ K*(r k)^2) :
    Tendsto (fun k => r k*Real.sqrt (|K|/((n:ℝ)-1))) atTop (𝓝 0) := by
  have hn1 : 0 < (n:ℝ)-1 := by
    have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hq : Tendsto (fun k => |K| * (r k)^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => mul_nonneg (abs_nonneg K) (sq_nonneg _)) _ hε
    intro k
    rw [abs_of_nonpos hK]
    linarith [hcurv k]
  have hs := (Real.continuous_sqrt.tendsto 0).comp hq
  have hd := hs.div_const (Real.sqrt ((n:ℝ)-1))
  change Tendsto (fun k => Real.sqrt (|K| * (r k)^2)/Real.sqrt ((n:ℝ)-1))
    atTop (𝓝 (Real.sqrt 0/Real.sqrt ((n:ℝ)-1))) at hd
  have he (k : ℕ) : Real.sqrt (|K| * (r k)^2)/Real.sqrt ((n:ℝ)-1) =
      r k*Real.sqrt (|K|/((n:ℝ)-1)) := by
    rw [Real.sqrt_mul (abs_nonneg K),Real.sqrt_sq (hr k),
      Real.sqrt_div (abs_nonneg K)]
    ring
  simpa only [he,Real.sqrt_zero,zero_div] using hd

theorem midpointFloor_real_tendsto_half {K d : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hK : K ≤ 0) {r ε : ℕ → ℝ}
    (hr : ∀ k, 0 ≤ r k) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -ε k ≤ K*(r k)^2) :
    Tendsto (fun k => (midpointFloor K n (d*r k)).toReal) atTop (𝓝 (1/2)) := by
  have harg := (curvature_scaled_sqrt_tendsto_zero hn hK hr hε hcurv).const_mul d
  have heq (k : ℕ) : (midpointFloor K n (d*r k)).toReal =
      1/(2*Real.cosh (d*(r k*Real.sqrt (|K|/((n:ℝ)-1))))) := by
    simp only [midpointFloor,mul_assoc]
    rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [heq]
  have hc := (Real.continuous_cosh.tendsto 0).comp (by simpa only [mul_zero] using harg)
  have hden := hc.const_mul 2
  have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).div hden
    (by norm_num : (2:ℝ)*Real.cosh 0 ≠ 0)
  change Tendsto (fun k => 1/(2*Real.cosh (d*(r k*Real.sqrt (|K|/((n:ℝ)-1))))))
    atTop (𝓝 (1/(2*Real.cosh 0))) at hh
  simpa only [Real.cosh_zero,mul_one] using hh

end RegularPointCoordinates

end

end OAI
