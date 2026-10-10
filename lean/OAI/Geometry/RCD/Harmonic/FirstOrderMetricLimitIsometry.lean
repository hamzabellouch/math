import OAI.Geometry.RCD.Metric.FiniteMetricValues
import OAI.Geometry.RCD.Transport.FirstOrderUniformDistortion

namespace OAI

/-! # The original coordinate limit is locally isometric on the metric limit -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [MetricSpace Y]

theorem NoncollapsedRCD.first_order_metric_limit_isometry {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p : ℕ → X) (r ε δ : ℕ → ℝ) (V : ℕ → X → Y) (q : Y)
    (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1≤K*(80*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) 5 (δ k) (V k))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (80*r k) (ε k) (u k) (v k))
    (g : Fin n → Y → ℝ) (hg : ∀ i, Continuous (g i))
    (hvalues : ∀ i η, 0<η → ∀ᶠ k in atTop, ∀ x, dist x (p k)≤5*r k →
      |(v k x i-v k (p k) i)/r k-g i (V k x)|<η) :
    ∀ y z, dist y q<1/16 → dist z q<1/16 →
      dist (WithLp.toLp 2 (fun i => g i y)) (WithLp.toLp 2 (fun i => g i z))=dist y z := by
  let w k x := (r k)⁻¹ • (v k x-v k (p k))
  let F y := WithLp.toLp 2 (fun i => g i y)
  have hF : Continuous F := (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp (continuous_pi hg)
  have hw (k : ℕ) (x y : X) : dist (w k x) (w k y)=dist (v k x) (v k y)/r k := by
    dsimp [w]
    rw [dist_smul₀,Real.norm_of_nonneg (inv_pos.mpr (hr k)).le,dist_sub_right,div_eq_inv_mul]
  apply metric_limit_distance_identification p r δ V w F hr hδ0 hV
    (by norm_num : (1/16:ℝ)<5) hF
  · have hvw := finite_metric_value_limit p r V w g (fun i η hη => by
      simpa only [w,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,div_eq_inv_mul] using hvalues i η hη)
    intro η hη
    filter_upwards [hvw η hη] with k hk
    intro x hx
    exact hk x (hx.trans (by nlinarith [hr k] : (1/16:ℝ)*r k≤5*r k))
  · intro η hη
    have hs (k : ℕ) : FirstOrderSplittingOn (hausdorff n X) hX.quadratic
        (p k) (16*(5*r k)) (ε k) (u k) (v k) := by
      simpa only [show (16:ℝ)*(5*r k)=80*r k by ring] using hsplit k
    have hc (k : ℕ) : -1≤K*(16*(5*r k))^2 := by
      simpa only [show (16:ℝ)*(5*r k)=80*r k by ring] using hcurv k
    have hr' : Tendsto (fun k => 5*r k) atTop (𝓝 0) := by
      simpa only [mul_zero] using hr0.const_mul 5
    have hd := hX.first_order_uniform_distortion hn hK p (fun k => 5*r k) ε
      (fun k => mul_pos (by norm_num) (hr k)) hr' hc hε hε1 hε0 u v hs
      (show 0<η/5 by positivity)
    filter_upwards [hd] with k hk
    intro x y hx hy
    have hx' : dist x (p k)≤5*r k/48 := hx.trans (by nlinarith [hr k])
    have hy' : dist y (p k)≤5*r k/48 := hy.trans (by nlinarith [hr k])
    have hh := hk x y hx' hy'
    rw [hw]
    have he : dist (v k x) (v k y)/r k-dist x y/r k=
        5*(dist (v k x) (v k y)/(5*r k)-dist x y/(5*r k)) := by field_simp
    rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<5)]
    linarith

end RegularPointCoordinates

end

end OAI
