import OAI.Probability.ContinuumTransition.UpperPressure

namespace OAI

section
open scoped Topology BigOperators
open Filter
namespace ContinuumTemperature

theorem physical_kac_upper_eventually {C : NNReal} (hC : LipschitzWith C kernel)
    {t β a : ℝ} (ht : 1 < t) (hβ : 0 < β) (ha : 0 ≤ a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(a+∑' n, σ n) ≤ (t^2/8)/8)
    (hgap : t*a/2 < (t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hbound : ∀ n, σ n ≠ 0 → R n ≤ R₀)
    (h : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop,
      physicalPressure (physicalProfile t (prepend a σ) (prepend (((q : ℝ)/4)^2) R)) t (β,h) ≤
        quadraticPressure (physicalProfile t σ R) β (t*h) (β*(t*a)/2)/t+ε := by
  have ht0 := lt_trans zero_lt_one ht
  have hσsum : 0 ≤ ∑' n, σ n := tsum_nonneg hσ
  have hK := kernelHeight_pos.le
  have hta : 0 ≤ 2197*t*kernelHeight*a := by positivity
  have hsm : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8 := by
    nlinarith only [hsmall, hta, sq_nonneg t]
  have hgap' : β*(t*a)/2 < β*((t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64) := by
    simpa only [mul_div_assoc] using mul_lt_mul_of_pos_left hgap hβ
  let aL : ℝ → ℝ := fun L => β*(t*a)*(1+kacRowError C (L^2) L)/2
  have haL : Tendsto aL atTop (𝓝 (β*(t*a)/2)) := by
    have hh := (((kacRowError_sq_tendsto C).const_add 1).const_mul (β*(t*a))).div_const 2
    simpa only [add_zero, mul_one] using hh
  have hquad := (quadraticGrand_pressure_tendsto (μ := t*h) ht hβ.le hσ hR hs hsm hgap' haL).div_const t
  have hL : Tendsto (fun q : ℕ => (q : ℝ)/4) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
  have hcoeff := haL.eventually_lt
    (coerciveCoefficient_tendsto (β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)))
    (by simpa only [mul_div_assoc] using hgap')
  let E := β*(momentConstant t β (t*h)/2)*(2197*t*kernelHeight*(∑' n, σ n))/t
  have hbdy : Tendsto (fun q : ℕ => E*(384*((cellRadius R₀).toNat : ℝ)/(q : ℝ))) atTop (𝓝 0) := by
    have hh := ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
      (384*((cellRadius R₀).toNat : ℝ))).const_mul E
    simpa only [Function.comp_apply, mul_zero, div_eq_mul_inv] using hh
  have hright := (hquad.comp hL).add hbdy
  have he := hright.eventually_lt_const (by linarith :
    quadraticPressure (physicalProfile t σ R) β (t*h) (β*(t*a)/2)/t+0 <
      quadraticPressure (physicalProfile t σ R) β (t*h) (β*(t*a)/2)/t+ε)
  filter_upwards [hL.eventually hcoeff, he, eventually_ge_atTop (4 : ℕ)] with q hc he hq
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hu : 1 ≤ (q : ℝ)/4 := by
    have hq4 : (4 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hS : 1 ≤ ((q : ℝ)/4)^2 := by nlinarith
  have hh := physical_kac_pressure_upper hC ht hβ ha hS hσ hR hs hsmall hR₀ hbound hq0 hc.le h
  apply hh.trans
  simpa only [Function.comp_apply, aL, E, div_div, mul_comm t] using he.le

end ContinuumTemperature
end

end OAI
