import OAI.Geometry.RCD.Transport.MeasuredTransportData
import OAI.Geometry.RCD.Transport.PrescribedPlanCompression

namespace OAI

/-! # Compression controlled by the actual nearby endpoint images -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem MeasuredTransportData.short_endpoint_distance_bound {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X}
    {p : ℕ → X} {r ε : ℕ → ℝ} {S τ η : ℝ} {v : ℕ → X → Euclidean n}
    {α β : ProbabilityMeasure (Euclidean n)} {c₀ : ℝ}
    (D : MeasuredTransportData hX p r S τ v α β c₀)
    (hτS : τ≤S) (hr : ∀ k, 0<r k)
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (z : Euclidean n)
    (hz0 : ∀ k, ∀ᵐ x ∂(D.left k : Measure X), v (k+D.offset) x∈closedBall z η)
    (hz1 : ∀ k, ∀ᵐ x ∂(D.right k : Measure X), v (k+D.offset) x∈closedBall z η)
    (k : ℕ) : OptimalPlanDistanceBound (D.left k : Measure X) (D.right k : Measure X)
      ((2*η+ε (k+D.offset))*r (k+D.offset)) := by
  intro π hπ _ hp
  let : IsProbabilityMeasure π := hπ
  have hend := optimalPlan_endpoints (D.left k : Measure X) (D.right k : Measure X) π hp
  have h0 := ae_of_ae_map (measurable_path_eval 0).aemeasurable (hend.1.symm ▸ D.left_support k)
  have h1 := ae_of_ae_map (measurable_path_eval 1).aemeasurable (hend.2.symm ▸ D.right_support k)
  have hz0' := ae_of_ae_map (measurable_path_eval 0).aemeasurable (hend.1.symm ▸ hz0 k)
  have hz1' := ae_of_ae_map (measurable_path_eval 1).aemeasurable (hend.2.symm ▸ hz1 k)
  filter_upwards [h0,h1,hz0',hz1'] with γ hγ0 hγ1 hγz0 hγz1
  have hrad := mul_le_mul_of_nonneg_right hτS (hr (k+D.offset)).le
  have he := (abs_le.mp ((hv (k+D.offset)).metric.2.1 _ _
    (hγ0.trans hrad) (hγ1.trans hrad))).1
  have him : dist (v (k+D.offset) (γ 0)) (v (k+D.offset) (γ 1))≤2*η := by
    have hh := dist_triangle (v (k+D.offset) (γ 0)) z (v (k+D.offset) (γ 1))
    rw [dist_comm z (v (k+D.offset) (γ 1))] at hh
    change dist (v (k+D.offset) (γ 0)) z≤η at hγz0
    change dist (v (k+D.offset) (γ 1)) z≤η at hγz1
    linarith
  exact (div_le_iff₀ (hr (k+D.offset))).mp (by linarith)

theorem MeasuredTransportData.short_endpoint_compression {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} (hn : 2≤n)
    {p : ℕ → X} {r ε : ℕ → ℝ} {S τ η : ℝ} {v : ℕ → X → Euclidean n}
    {α β : ProbabilityMeasure (Euclidean n)} {c₀ : ℝ}
    (D : MeasuredTransportData hX p r S τ v α β c₀)
    (hS : 0<S) (hτ : 0≤τ) (hτS : τ≤S) (hη : 0≤η)
    (hr : ∀ k, 0<r k) (hε : ∀ k, 0≤ε k)
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (z : Euclidean n)
    (hz0 : ∀ k, ∀ᵐ x ∂(D.left k : Measure X), v (k+D.offset) x∈closedBall z η)
    (hz1 : ∀ k, ∀ᵐ x ∂(D.right k : Measure X), v (k+D.offset) x∈closedBall z η)
    (k : ℕ) (t : Time) :
    (D.plan k : Measure C(Time,X)).map (fun γ => γ t)≤
      compressionBudget K n ((2*η+ε (k+D.offset))*r (k+D.offset))
        (ENNReal.ofReal (D.control k)*
          (hausdorff n X (ball (p (k+D.offset)) (S*r (k+D.offset))))⁻¹) • hausdorff n X := by
  let μ := hausdorff n X
  let C := ENNReal.ofReal (D.control k)*(μ (ball (p (k+D.offset)) (S*r (k+D.offset))))⁻¹
  have hC : C≠⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.mpr (hX.fullSupport _ _ (mul_pos hS (hr _))).ne')
  have hd := D.short_endpoint_distance_bound hτS hr hv z hz0 hz1 k
  exact hX.prescribed_plan_compression hn (D.left k) (D.right k) hC
    (compressionBudget_ne_top K n (2*(τ*r (k+D.offset))) hC)
    (D.left_bound k) (D.right_bound k) (p (k+D.offset))
    (mul_nonneg hτ (hr _).le)
    (mul_nonneg (add_nonneg (mul_nonneg (by norm_num) hη) (hε _)) (hr _).le)
    (D.left_support k) (D.right_support k) hd (D.plan k) (D.geodesic k) (D.optimal k)
    (D.compression k) t

end RegularPointCoordinates

end

end OAI
