import OAI.Geometry.RCD.Harmonic.FirstOrderInteriorRestriction
import OAI.Geometry.RCD.Harmonic.FirstOrderNoSupport

namespace OAI

/-! # Excluding vanishing supporting errors at moving interior centers -/

open Set Filter Metric MeasureTheory
open scoped Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_moving_no_support {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p q : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1≤K*(80*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hs : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (80*r k) (ε k) (u k) (v k))
    (hqp : ∀ᶠ k in atTop, dist (q k) (p k)≤r k/128)
    {c : ℝ} (hc : 0<c) (hc1 : c≤1/128) (a : Euclidean n) (ha : ‖a‖=1)
    (hsupport : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ x∈ball (q k) (c*r k/48),
      ⟪v k x-v k (q k),a⟫_ℝ≤η*r k) : False := by
  obtain ⟨D,hD,hrestrict⟩ := hX.first_order_interior_restriction hn hc (by linarith)
  obtain ⟨C,_hC,hthreshold⟩ := hX.first_order_support_threshold hn
  have hr5 : ∀ k, 0<5*r k := fun k => mul_pos (by norm_num) (hr k)
  have hcurv5 : ∀ k, -1≤K*(16*(5*r k))^2 := by
    intro k
    simpa only [show 16*(5*r k)=80*r k by ring] using hcurv k
  have hm := hX.first_order_uniform_distortion hn hK p (fun k => 5*r k) ε hr5
    (by simpa using hr0.const_mul 5) hcurv5 hε hε1 hε0 u v
    (by intro k; simpa only [show 16*(5*r k)=80*r k by ring] using hs k)
    (show 0<c/(5*4096) by positivity)
  have hDe : Tendsto (fun k => D*ε k) atTop (𝓝 0) := by
    simpa using hε0.const_mul D
  have hlower : ∀ᶠ k in atTop, 1≤C*(D*ε k) := by
    filter_upwards [hqp,hm,hsupport (c/4096) (by positivity),
      hDe.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with k hq hmetric hsup hsmall
    have hq1 : dist (q k) (p k)≤r k := by linarith [hr k]
    have hcr : 0<c*r k := mul_pos hc (hr k)
    have hlocal := hrestrict (p k) (q k) (r k) (ε k) (hr k) (hcurv k) hq1 (hε k)
      (u k) (v k) (hs k)
    have hcurvc : -1≤K*(16*(c*r k))^2 := by
      have hh : (16*(c*r k))^2≤(80*r k)^2 := by
        have hcr' : c*r k≤r k := mul_le_of_le_one_left (hr k).le (by linarith)
        nlinarith [sq_nonneg (16*(c*r k)),sq_nonneg (80*r k)]
      exact (hcurv k).trans (mul_le_mul_of_nonpos_left hh hK)
    apply hthreshold (q k) (c*r k) (D*ε k) hcr hcurvc
      (mul_nonneg (by linarith) (hε k)) hsmall.le (u k) (v k) hlocal a ha
    · intro x hx
      have hxp : dist x (p k)≤5*r k/48 := by
        have hh := dist_triangle x (q k) (p k)
        change dist x (q k)<c*r k/48 at hx
        have hh' : c*r k≤r k/128 := by
          nlinarith [mul_le_mul_of_nonneg_right hc1 (hr k).le]
        linarith [hr k]
      have hqp5 : dist (q k) (p k)≤5*r k/48 := by linarith [hr k]
      have hh := hmetric x (q k) hxp hqp5
      rw [← sub_div,abs_div] at hh
      rw [abs_of_pos (hr5 k)] at hh
      have hh' := (div_le_iff₀ (hr5 k)).mp hh
      rw [← dist_eq_norm,← sub_div,abs_div,abs_of_pos hcr]
      apply (div_le_iff₀ hcr).mpr
      nlinarith [hh']
    · intro x hx
      have hh := hsup x hx
      convert hh using 1
      ring
  have hzero : Tendsto (fun k => C*(D*ε k)) atTop (𝓝 0) := by
    simpa using hDe.const_mul C
  have hh : (1:ℝ)≤0 := le_of_tendsto_of_tendsto tendsto_const_nhds hzero hlower
  norm_num at hh

end RegularPointCoordinates

end

end OAI
