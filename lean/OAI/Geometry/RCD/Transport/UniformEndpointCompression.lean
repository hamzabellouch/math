import OAI.Geometry.RCD.Transport.ShortEndpointCompression
import OAI.Geometry.RCD.Transport.CurvatureCompressionBound

namespace OAI

/-! # A scale-uniform compression factor for nearby Euclidean endpoint images -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem MeasuredTransportData.uniform_endpoint_compression {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} (hn : 2≤n)
    {p : ℕ → X} {r ε : ℕ → ℝ} {S τ η : ℝ} {v : ℕ → X → Euclidean n}
    {α β : ProbabilityMeasure (Euclidean n)} {c₀ : ℝ}
    (D : MeasuredTransportData hX p r S τ v α β c₀)
    (hS : 0<S) (hτ : 0≤τ) (hτS : τ≤S) (hη : 0≤η)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2) (hε : ∀ k, 0≤ε k)
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (z : Euclidean n)
    (hz0 : ∀ k, ∀ᵐ x ∂(D.left k : Measure X), v (k+D.offset) x∈closedBall z η)
    (hz1 : ∀ k, ∀ᵐ x ∂(D.right k : Measure X), v (k+D.offset) x∈closedBall z η)
    (k : ℕ) (t : Time) :
    (D.plan k : Measure C(Time,X)).map (fun γ => γ t)≤
      (ENNReal.ofReal (Real.exp ((n:ℝ)*2*(2*η+ε (k+D.offset)))*D.control k)*
        (hausdorff n X (ball (p (k+D.offset)) (S*r (k+D.offset))))⁻¹) • hausdorff n X := by
  let μ := hausdorff n X
  let C := ENNReal.ofReal (D.control k)*(μ (ball (p (k+D.offset)) (S*r (k+D.offset))))⁻¹
  have hC : C≠⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.mpr (hX.fullSupport _ _ (mul_pos hS (hr _))).ne')
  have hh := hX.prescribed_plan_uniform_compression hn
    (D.left k : Measure X) (D.right k : Measure X) hC
    (compressionBudget_ne_top K n (2*(τ*r (k+D.offset))) hC)
    (D.left_bound k) (D.right_bound k) (p (k+D.offset))
    (mul_nonneg hτ (hr _).le) (add_nonneg (mul_nonneg (by norm_num) hη) (hε (k+D.offset)))
    (hr (k+D.offset)).le (hcurv (k+D.offset))
    (D.left_support k) (D.right_support k)
    (D.short_endpoint_distance_bound hτS hr hv z hz0 hz1 k)
    (D.plan k : Measure C(Time,X)) (D.geodesic k) (D.optimal k) (D.compression k) t
  simpa only [C,μ,← mul_assoc,← ENNReal.ofReal_mul (Real.exp_nonneg _)] using hh

end RegularPointCoordinates

end

end OAI
