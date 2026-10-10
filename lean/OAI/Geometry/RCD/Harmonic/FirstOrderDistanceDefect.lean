import OAI.Geometry.RCD.Sobolev.FirstOrderTestMetricDefect
import OAI.Geometry.RCD.Metric.InwardDistance

namespace OAI

/-! # The original first-order coordinates asymptotically recover distance -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_distance_defect {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p x y : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1≤K*(16*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k))
    (hx : ∀ k, dist (x k) (p k)≤r k/48) (hy : ∀ k, dist (y k) (p k)≤r k/48) :
    Tendsto (fun k => max 0 (dist (x k) (y k)/r k-
      dist (v k (x k)) (v k (y k))/r k)) atTop (𝓝 0) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let W k := inwardSobolev μ Q (x k) (r k)
  let V k := inwardDistance (x k) (r k)
  let A (k : ℕ) : ℝ≥0 := ⟨r k,(hr k).le⟩
  have hrep (k : ℕ) : V k =ᵐ[μ] SobolevSpace.toLp μ Q (W k) :=
    (inwardSobolev_coe μ Q (x k) (r k)).symm
  have hA (k : ℕ) : ∀ᵐ z ∂μ, |SobolevSpace.toLp μ Q (W k) z|≤A k := by
    filter_upwards [inwardSobolev_bounds μ Q (x k) (hr k).le] with z hz
    change |SobolevSpace.toLp μ Q (W k) z|≤r k
    change 0≤SobolevSpace.toLp μ Q (W k) z ∧ SobolevSpace.toLp μ Q (W k) z≤r k at hz
    rw [abs_of_nonneg hz.1]
    exact hz.2
  have hlim := hX.first_order_test_metric_defect hn hK p x y r ε hr hr0 hcurv hε hε1 hε0
    u v hsplit hx hy (fun k => SobolevSpace.toLp μ Q (W k)) V 1 1 A
    (fun k => inwardDistance_lipschitz (x k) (r k))
    (fun k => inwardDistance_compact (x k) (r k)) hrep hA (fun k => by change r k≤1*r k; simp)
  have hval (k : ℕ) : |V k (y k)-V k (x k)|=dist (x k) (y k) := by
    have hd : dist (x k) (y k)≤r k := by
      have hh := dist_triangle (x k) (p k) (y k)
      rw [dist_comm (p k) (y k)] at hh
      linarith [hx k,hy k,hr k]
    simp only [V,inwardDistance,dist_self,sub_zero,max_eq_left (hr k).le,
      max_eq_left (sub_nonneg.mpr hd),sub_sub_cancel_left,abs_neg,abs_of_nonneg dist_nonneg]
  simpa only [hval,NNReal.coe_one,one_mul] using hlim

end RegularPointCoordinates

end

end OAI
