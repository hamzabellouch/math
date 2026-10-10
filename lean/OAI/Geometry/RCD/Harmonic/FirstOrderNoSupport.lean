import OAI.Geometry.RCD.Harmonic.FirstOrderSupportThreshold
import OAI.Geometry.RCD.Transport.FirstOrderUniformDistortion

namespace OAI

/-! # No limiting supporting halfspace for the original coordinate images -/

open Set Filter MeasureTheory Metric
open scoped Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_no_asymptotic_support {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1≤K*(16*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k))
    (a : ℕ → Euclidean n) (ha : ∀ k, ‖a k‖=1)
    (b : ℕ → ℝ) (hb0 : Tendsto b atTop (𝓝 0))
    (hsupport : ∀ k x, x∈ball (p k) (r k/48) →
      ⟪v k x-v k (p k),a k⟫_ℝ≤b k*r k) : False := by
  obtain ⟨C,_hC,hthreshold⟩ := hX.first_order_support_threshold hn
  have hm := hX.first_order_uniform_distortion hn hK p r ε hr hr0 hcurv hε hε1 hε0 u v hsplit
    (by norm_num : (0:ℝ)<1/4096)
  have hlower : ∀ᶠ k in atTop, 1≤C*ε k := by
    filter_upwards [hm,hb0.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4096))] with k hk hbk
    apply hthreshold (p k) (r k) (ε k) (hr k) (hcurv k) (hε k) (hε1 k)
      (u k) (v k) (hsplit k) (a k) (ha k)
    · intro x hx
      have hp : dist (p k) (p k)≤r k/48 := by
        simp only [dist_self]
        exact div_nonneg (hr k).le (by norm_num)
      simpa only [dist_eq_norm] using hk x (p k) (le_of_lt hx) hp
    · intro x hx
      have hh := (hsupport k x hx).trans (mul_le_mul_of_nonneg_right hbk.le (hr k).le)
      simpa only [one_div_mul_eq_div] using hh
  have hlimit : Tendsto (fun k => C*ε k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hε0.const_mul C
  have hh : (1:ℝ)≤0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlimit hlower
  norm_num at hh

end RegularPointCoordinates

end

end OAI
